-- Prove2me | solution 1 for HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bbbae219-4c2d-574e-ba90-5283f86f7e76

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_CartierDual_exists_algHomEquiv_groupLike
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfPoints

private theorem eval_bijective_of_card_eq_finrank_of_residue_comp_ne
    {O : Type} [CommRing O] [IsLocalRing O]
    {B : Type} [CommRing B] [Algebra O B] [Module.Finite O B] [Module.Free O B]
    {ι : Type} [Fintype ι] (φ : ι → (B →ₐ[O] O))
    (hcard : Fintype.card ι = Module.finrank O B)
    (hdist : ∀ i j, i ≠ j →
      (IsLocalRing.residue O).comp (φ i).toRingHom ≠ (IsLocalRing.residue O).comp (φ j).toRingHom) :
    Function.Bijective (fun b : B => fun i : ι => φ i b) := by
  classical
  let ψ : ι → (B →+* IsLocalRing.ResidueField O) := fun i => (IsLocalRing.residue O).comp (φ i).toRingHom
  have hψapp : ∀ i b, ψ i b = IsLocalRing.residue O (φ i b) := fun i b => rfl
  have hψalg : ∀ i (o : O), ψ i (algebraMap O B o) = IsLocalRing.residue O o := by
    intro i o
    rw [hψapp, AlgHom.commutes, Algebra.algebraMap_self_apply]
  have hψsurj : ∀ i, Function.Surjective (ψ i) := by
    intro i r
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨algebraMap O B o, hψalg i o⟩
  have hmax : ∀ i, (RingHom.ker (ψ i)).IsMaximal :=
    fun i => RingHom.ker_isMaximal_of_surjective (ψ i) (hψsurj i)
  have hker : ∀ i j, i ≠ j → RingHom.ker (ψ i) ≠ RingHom.ker (ψ j) := by
    intro i j hij hK
    apply hdist i j hij
    refine RingHom.ext fun b => ?_
    show ψ i b = ψ j b
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (ψ i b)
    have hb : b - algebraMap O B o ∈ RingHom.ker (ψ i) := by
      rw [RingHom.mem_ker, map_sub, hψalg, ho, sub_self]
    rw [hK, RingHom.mem_ker, map_sub, sub_eq_zero, hψalg] at hb
    rw [hb, ho]
  have hcop : Pairwise (Function.onFun IsCoprime fun i => RingHom.ker (ψ i)) := by
    intro i j hij
    show IsCoprime (RingHom.ker (ψ i)) (RingHom.ker (ψ j))
    haveI := hmax i
    haveI := hmax j
    exact Ideal.isCoprime_of_isMaximal (hker i j hij)
  have hΨ : ∀ c : ι → O, ∃ b : B, ∀ i, ψ i b = IsLocalRing.residue O (c i) := by
    intro c
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hcop
      (fun i => Ideal.Quotient.mk (RingHom.ker (ψ i)) (algebraMap O B (c i)))
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨b, fun i => ?_⟩
    have hi := congrFun hx i
    rw [Ideal.quotientInfToPiQuotient_mk', Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero] at hi
    rw [hi, hψalg]
  let ev : B →ₗ[O] (ι → O) := LinearMap.pi fun i => (φ i).toLinearMap
  have hev : ∀ b i, ev b i = φ i b := fun b i => rfl
  have hsurj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top]
    have hN : (⊤ : Submodule O (ι → O)) ≤ LinearMap.range ev ⊔ (IsLocalRing.maximalIdeal O) • ⊤ := by
      intro c _
      obtain ⟨b, hb⟩ := hΨ c
      have hcoord : ∀ i, (c - ev b) i ∈ IsLocalRing.maximalIdeal O := by
        intro i
        rw [← IsLocalRing.residue_eq_zero_iff, Pi.sub_apply, map_sub, hev, ← hψapp, hb, sub_self]
      have hdiff : c - ev b ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O (ι → O)) := by
        rw [pi_eq_sum_univ (c - ev b)]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) Submodule.mem_top
      have hsplit : ev b + (c - ev b) = c := add_sub_cancel _ _
      rw [← hsplit]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self ev b) hdiff
    exact top_le_iff.mp
      (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) hN)
  have hrank : Module.finrank O (ι → O) = Module.finrank O B := by
    rw [Module.finrank_pi, hcard]
  let e : (ι → O) ≃ₗ[O] B := LinearEquiv.ofFinrankEq (ι → O) B hrank
  have hg : Function.Surjective ((e : (ι → O) →ₗ[O] B) ∘ₗ ev) := e.surjective.comp hsurj
  have hginj : Function.Injective ((e : (ι → O) →ₗ[O] B) ∘ₗ ev) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hg
  have hinj : Function.Injective ev := by
    intro b₁ b₂ h
    exact hginj (show e (ev b₁) = e (ev b₂) by rw [h])
  have hevf : (fun b : B => fun i : ι => φ i b) = ⇑ev := by
    funext b i
    exact (hev b i).symm
  rw [hevf]
  exact ⟨hinj, hsurj⟩

variable {O : Type} [CommRing O] {H : Type} [CommRing H] [HopfAlgebra O H]
variable {L : Type} [Field L] [Algebra O L]

private noncomputable def evalAt (p : H →ₐ[O] L) : L ⊗[O] H →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) p (fun _ _ => Commute.all _ _)

@[scoped simp] private theorem evalAt_tmul (p : H →ₐ[O] L) (c : L) (h : H) : evalAt p (c ⊗ₜ h) = c * p h := by
  simp [evalAt]

private theorem evalAt_map_twist (τ : L →ₐ[O] L) (p p' : H →ₐ[O] L) (hpp' : ∀ h, p h = τ (p' h)) (x : L ⊗[O] H) :
    evalAt p (Algebra.TensorProduct.map τ (AlgHom.id O H) x) = τ (evalAt p' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c h => simp [hpp', map_mul]
  | add x y hx hy => simp [map_add, hx, hy]

private theorem evalAt_convMul (p p' : WithConv (H →ₐ[O] L)) (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
    evalAt (WithConv.ofConv (p * p')) x = evalAt (WithConv.ofConv p) x * evalAt (WithConv.ofConv p') x := by
  let E : (L ⊗[O] H) ⊗[L] (L ⊗[O] H) →ₐ[L] L :=
    Algebra.TensorProduct.productMap (evalAt (WithConv.ofConv p)) (evalAt (WithConv.ofConv p'))
  have hkey : (evalAt (WithConv.ofConv (p * p'))).toLinearMap
      = E.toLinearMap ∘ₗ Coalgebra.comul (R := L) (A := L ⊗[O] H) := by
    refine TensorProduct.AlgebraTensorModule.ext fun c h => ?_
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply, evalAt_tmul,
      AlgHom.convMul_apply]
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    induction (Coalgebra.comul (R := O) h) using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
    | tmul a b =>
        rw [Algebra.TensorProduct.lift_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
        simp only [E, Algebra.TensorProduct.productMap_apply_tmul, evalAt_tmul, one_mul]
        ring
    | add s t hs ht =>
        rw [map_add, mul_add, hs, ht, TensorProduct.tmul_add, map_add, map_add]
  have := congrArg (fun f : L ⊗[O] H →ₗ[L] L => f x) hkey
  simp only [AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply] at this
  rw [this, hx.comul_eq_tmul_self]
  simp [E, Algebra.TensorProduct.productMap_apply_tmul]

private theorem evalAt_one (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
    evalAt (WithConv.ofConv (1 : WithConv (H →ₐ[O] L))) x = 1 := by
  have hkey : (evalAt (WithConv.ofConv (1 : WithConv (H →ₐ[O] L)))).toLinearMap
      = Coalgebra.counit (R := L) (A := L ⊗[O] H) := by
    refine TensorProduct.AlgebraTensorModule.ext fun c h => ?_
    simp only [AlgHom.toLinearMap_apply, evalAt_tmul]
    rw [TensorProduct.counit_tmul, CommSemiring.counit_apply]
    show c * (1 : WithConv (H →ₐ[O] L)) h = Coalgebra.counit (R := O) h • c
    rw [AlgHom.convOne_apply, Algebra.smul_def, mul_comm]
  have := congrArg (fun f : L ⊗[O] H →ₗ[L] L => f x) hkey
  simp only [AlgHom.toLinearMap_apply] at this
  rw [this, hx.counit_eq_one]

private theorem evalAt_pow (p : WithConv (H →ₐ[O] L)) (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) (k : ℕ) :
    evalAt (WithConv.ofConv (p ^ k)) x = (evalAt (WithConv.ofConv p) x) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, evalAt_one x hx]
  | succ k ih => rw [pow_succ, pow_succ, evalAt_convMul _ _ x hx, ih]

private theorem eval_injective [Nontrivial O] [Module.Finite O H] [Module.Free O H]
    {ι : Type} [Fintype ι] (pts : ι → (H →ₐ[O] L)) (hinj : Function.Injective pts)
    (hcard : Fintype.card ι = Module.finrank O H) :
    ∀ x y : L ⊗[O] H, (∀ i, evalAt (pts i) x = evalAt (pts i) y) → x = y := by
  have hcard' : Fintype.card ι = Module.finrank L (L ⊗[O] H) := by
    rw [Module.finrank_baseChange, hcard]
  have hdist : ∀ i j, i ≠ j →
      (IsLocalRing.residue L).comp (evalAt (pts i)).toRingHom ≠ (IsLocalRing.residue L).comp (evalAt (pts j)).toRingHom := by
    intro i j hij hEq
    apply hij
    apply hinj
    refine AlgHom.ext fun h => ?_
    have hres : Function.Injective (IsLocalRing.residue L) := by
      rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_eq_bot]
    have := congrArg (fun f : L ⊗[O] H →+* IsLocalRing.ResidueField L => f (1 ⊗ₜ h)) hEq
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, evalAt_tmul,
      one_mul] at this
    exact hres this
  have hbij := eval_bijective_of_card_eq_finrank_of_residue_comp_ne (O := L) (B := L ⊗[O] H)
    (fun i => evalAt (pts i)) hcard' hdist
  intro x y hxy
  exact hbij.1 (funext hxy)

private theorem map_twist_eq_self_of_isGroupLikeElem [Nontrivial O] [Module.Finite O H] [Module.Free O H]
    {ι : Type} [Fintype ι] (pts : ι → (H →ₐ[O] L)) (hinj : Function.Injective pts)
    (hcard : Fintype.card ι = Module.finrank O H)
    (m : ℕ) (hm : ∀ x : L ⊗[O] H, IsGroupLikeElem L x → x ^ m = 1)
    (τ τ' : L →ₐ[O] L) (hττ' : ∀ z, τ (τ' z) = z)
    (c' : ℕ)
    (hτ'ζ : ∀ ζ : L, ζ ^ m = 1 → τ' ζ = ζ ^ c')
    (hτ'pts : ∀ f : WithConv (H →ₐ[O] L),
      WithConv.toConv (τ'.comp (WithConv.ofConv f)) = f ^ c')
    (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
    Algebra.TensorProduct.map τ (AlgHom.id O H) x = x := by
  refine eval_injective pts hinj hcard _ _ fun i => ?_
  set ζ := evalAt (pts i) x with hζ
  have hζm : ζ ^ m = 1 := by
    rw [hζ, ← map_pow, hm x hx, map_one]
  have hp' : ∀ h, pts i h = τ ((τ'.comp (pts i)) h) := fun h => (hττ' _).symm
  rw [evalAt_map_twist τ (pts i) (τ'.comp (pts i)) hp' x]
  have hconv : τ'.comp (pts i) = WithConv.ofConv ((WithConv.toConv (pts i)) ^ c') := by
    have := hτ'pts (WithConv.toConv (pts i))
    rw [WithConv.ofConv_toConv] at this
    rw [← this, WithConv.ofConv_toConv]
  rw [hconv, evalAt_pow _ x hx, WithConv.ofConv_toConv, ← hζ, ← hτ'ζ ζ hζm, hττ']

end HopfPoints
p2m_reactivate "P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub.HopfPoints"

namespace AlgHom p2m_export "AlgHom" "comp_convMul_distrib ext toLinearMap_apply commutes toLinearMap one_apply convOne_apply coe_toRingHom toLinearMap_convMul comp Finite.of_surjective mk toRingHom toRingHom_eq_coe card mem_range_self range_eq_top Finite commutes' coe_comp convMul_comp_bialgHom_distrib comp_apply convMul_apply mem_range" end AlgHom
p2m_open_scoped "AlgHom" in
private theorem AlgHom.apply_mem_valuationSubring_of_moduleFinite
    (A : ValuationSubring (AlgebraicClosure ℚ)) (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (H₁ : Type) [CommRing H₁] [Algebra ↥O H₁] [Module.Finite ↥O H₁]
    (f : H₁ →ₐ[↥O] AlgebraicClosure ℚ) (h : H₁) : f h ∈ A := by
  classical
  have hint : IsIntegral ↥O (f h) := (Algebra.IsIntegral.isIntegral (R := ↥O) h).map f
  obtain ⟨p, hpm, hpev⟩ := hint
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : A.valuation (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap ↥O (AlgebraicClosure ℚ) (p.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpev
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree, algebraMap ↥O (AlgebraicClosure ℚ) (p.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : A.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap ↥O (AlgebraicClosure ℚ) (p.coeff i) * f h ^ i) < A.valuation (f h) ^ p.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (algebraMap ↥O (AlgebraicClosure ℚ) (p.coeff i)) * A.valuation (f h) ^ i
        ≤ 1 * A.valuation (f h) ^ i := by
          exact mul_le_mul' ((A.valuation_le_one_iff _).mpr (hOA (p.coeff i).2)) le_rfl
      _ = A.valuation (f h) ^ i := one_mul _
      _ < A.valuation (f h) ^ p.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : A.valuation (f h ^ p.natDegree) < A.valuation (f h) ^ p.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk natCard_algHom_eq_finrank_of_charZero point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal exists_quotientFlag_of_galoisStableChain"
p2m_open "HopfAlgebra"

open HopfPoints

private theorem groupLike_pow_eq_one
    (q : ℕ) [Fact q.Prime]
    (O : Subring (AlgebraicClosure ℚ))
    (hOdvr : IsDiscreteValuationRing ↥O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (x : TensorProduct ↥O (AlgebraicClosure ℚ) H₀) (hx : IsGroupLikeElem (AlgebraicClosure ℚ) x) :
    x ^ q = 1 := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  let ι := H₀ →ₐ[↥O] AlgebraicClosure ℚ
  have hιcard : Nat.card ι = q ^ a := by
    rw [← hpts]
    exact Nat.card_congr ⟨WithConv.toConv, WithConv.ofConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite ι := Nat.finite_of_card_ne_zero (hιcard ▸ pow_ne_zero a hq0)
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank ↥O H₀ := by
    rw [Fintype.card_eq_nat_card, hιcard, hrank]
  refine eval_injective (fun f : ι => f) (fun _ _ h => h) hcard _ _ fun p => ?_
  rw [map_pow, map_one]
  have h1 := evalAt_pow (WithConv.toConv p) x hx q
  rw [hptq (WithConv.toConv p), WithConv.ofConv_toConv, evalAt_one x hx] at h1
  exact h1.symm

private theorem cartierDual_point_apply_fixed
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀] [Coalgebra.IsCocomm ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (ψ : CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ) (φ : CartierDual ↥O H₀) :
    σ (ψ φ) = ψ φ := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hσ' : σ⁻¹ ∈ A.inertiaSubgroupIn ℚ := Subgroup.inv_mem _ hσ
  let τ : AlgebraicClosure ℚ →ₐ[↥O] AlgebraicClosure ℚ :=
    { (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) with
      commutes' := fun o => (hOfix σ).mp hσ o o.2 }
  let τ' : AlgebraicClosure ℚ →ₐ[↥O] AlgebraicClosure ℚ :=
    { ((σ⁻¹ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) with
      commutes' := fun o => (hOfix σ⁻¹).mp hσ' o o.2 }
  have hτ : ∀ z, τ z = σ z := fun _ => rfl
  have hτ' : ∀ z, τ' z = σ⁻¹ z := fun _ => rfl
  have hττ' : ∀ z, τ (τ' z) = z := by
    intro z
    rw [hτ, hτ', AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  obtain ⟨c', hc'⟩ := AlgebraicClosure.exists_apply_eq_pow_of_pow_eq_one q hq0 σ⁻¹
  have hτ'ζ : ∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → τ' ζ = ζ ^ c' := fun ζ hζ => by
    rw [hτ']; exact hc' ζ hζ
  have hτ'pts : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ),
      WithConv.toConv (τ'.comp (WithConv.ofConv f)) = f ^ c' :=
    fun f => hχ σ⁻¹ hσ' c' hc' f _ (fun _ => rfl)
  let ι := H₀ →ₐ[↥O] AlgebraicClosure ℚ
  have hιcard : Nat.card ι = q ^ a := by
    rw [← hpts]
    exact Nat.card_congr ⟨WithConv.toConv, WithConv.ofConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite ι := Nat.finite_of_card_ne_zero (hιcard ▸ pow_ne_zero a hq0)
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank ↥O H₀ := by
    rw [Fintype.card_eq_nat_card, hιcard, hrank]
  obtain ⟨e, _he1, _he2, _he3, he4⟩ := CartierDual.exists_algHomEquiv_groupLike (↥O) H₀
  have hm : ∀ x : TensorProduct ↥O (AlgebraicClosure ℚ) H₀, IsGroupLikeElem (AlgebraicClosure ℚ) x → x ^ q = 1 :=
    fun x hx => groupLike_pow_eq_one q O hOdvr H₀ a hrank hpts hptq x hx
  have hfix : Algebra.TensorProduct.map τ (AlgHom.id ↥O H₀) (e (AlgebraicClosure ℚ) ψ).val
      = (e (AlgebraicClosure ℚ) ψ).val :=
    map_twist_eq_self_of_isGroupLikeElem (fun f : ι => f) (fun _ _ h => h) hcard q hm τ τ' hττ' c' hτ'ζ hτ'pts
      _ (e (AlgebraicClosure ℚ) ψ).isGroupLikeElem_val
  have hnat := he4 (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) τ ψ
  rw [hfix] at hnat
  have heq : e (AlgebraicClosure ℚ) (τ.comp ψ) = e (AlgebraicClosure ℚ) ψ := GroupLike.val_injective hnat
  have hψ : τ.comp ψ = ψ := (e (AlgebraicClosure ℚ)).injective heq
  have := DFunLike.congr_fun hψ φ
  rw [AlgHom.comp_apply, hτ] at this
  exact this

private theorem cartierDual_point_factors
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀] [Coalgebra.IsCocomm ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (ψ : CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ) :
    ∃ ψO : CartierDual ↥O H₀ →ₐ[↥O] ↥O, ∀ φ, ((ψO φ : ↥O) : AlgebraicClosure ℚ) = ψ φ := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  have hψO : ∀ φ, ψ φ ∈ O := fun φ =>
    hOmax _ (AlgHom.apply_mem_valuationSubring_of_moduleFinite A O hOA (CartierDual ↥O H₀) ψ φ)
      (fun σ hσ => cartierDual_point_apply_fixed q A O hOdvr hOfix H₀ a hrank hpts hptq hχ σ hσ ψ φ)
  refine ⟨{ toFun := fun φ => ⟨ψ φ, hψO φ⟩
            map_one' := Subtype.ext (map_one ψ)
            map_mul' := fun a b => Subtype.ext (map_mul ψ a b)
            map_zero' := Subtype.ext (map_zero ψ)
            map_add' := fun a b => Subtype.ext (map_add ψ a b)
            commutes' := fun r => Subtype.ext (ψ.commutes r) }, fun φ => rfl⟩

private theorem natCard_cartierDual_algHom_eq
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀] [Coalgebra.IsCocomm ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), (∀ h : H₀, g h = σ (f h)) → g = f ^ c) :
    Nat.card (CartierDual ↥O H₀ →ₐ[↥O] ↥O) = q ^ a := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  have hcardD : Nat.card (CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ) = q ^ a := by
    rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero, CartierDual.finrank_eq, hrank]
  rw [← hcardD]
  apply Nat.card_eq_of_bijective (fun ψO : CartierDual ↥O H₀ →ₐ[↥O] ↥O => (Algebra.ofId ↥O (AlgebraicClosure ℚ)).comp ψO)
  constructor
  · intro ψ₁ ψ₂ h
    refine AlgHom.ext fun φ => Subtype.ext ?_
    have := DFunLike.congr_fun h φ
    exact this
  · intro ψ
    obtain ⟨ψO, hψO⟩ := cartierDual_point_factors q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ ψ
    exact ⟨ψO, AlgHom.ext fun φ => hψO φ⟩

end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub.HopfPoints"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk natCard_algHom_eq_finrank_of_charZero point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal exists_quotientFlag_of_galoisStableChain"
p2m_open "HopfAlgebra"

open HopfPoints

private theorem cartierDual_point_pow_eq_one
    (q : ℕ) [Fact q.Prime]
    (O : Subring (AlgebraicClosure ℚ))
    (hOdvr : IsDiscreteValuationRing ↥O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀] [Coalgebra.IsCocomm ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (x : WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O)) : x ^ q = 1 := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  obtain ⟨e, _he1, he2, he3, _he4⟩ := CartierDual.exists_algHomEquiv_groupLike (↥O) H₀
  let Φ : WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O) → WithConv (CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ) :=
    fun y => WithConv.toConv ((Algebra.ofId ↥O (AlgebraicClosure ℚ)).comp (WithConv.ofConv y))
  have hΦmul : ∀ y z, Φ (y * z) = Φ y * Φ z := by
    intro y z
    show WithConv.toConv ((Algebra.ofId ↥O (AlgebraicClosure ℚ)).comp (WithConv.ofConv (y * z))) = _
    rw [AlgHom.comp_convMul_distrib]
  have hΦone : Φ 1 = 1 := by
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    rfl
  have hΦpow : ∀ y (m : ℕ), Φ (y ^ m) = Φ y ^ m := by
    intro y m
    induction m with
    | zero => rw [pow_zero, pow_zero, hΦone]
    | succ m ih => rw [pow_succ, pow_succ, hΦmul, ih]
  have hΦinj : ∀ y z, Φ y = Φ z → y = z := by
    intro y z hyz
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    have h1 := congrArg (fun g : WithConv (CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ) => g h) hyz
    have h2 : ((WithConv.ofConv y h : ↥O) : AlgebraicClosure ℚ) = (WithConv.ofConv z h : ↥O) := h1
    exact Subtype.ext h2
  let E' : WithConv (CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ)
      → GroupLike (AlgebraicClosure ℚ) (TensorProduct ↥O (AlgebraicClosure ℚ) H₀) :=
    fun y => e (AlgebraicClosure ℚ) (WithConv.ofConv y)
  have hE'mul_val : ∀ y z, (E' (y * z)).val = (E' y).val * (E' z).val := fun y z =>
    he3 (AlgebraicClosure ℚ) (WithConv.ofConv y) (WithConv.ofConv z) (WithConv.ofConv (y * z)) (AlgHom.toLinearMap_convMul y z)
  have hE'one_val : (E' 1).val = 1 := by
    refine he2 (AlgebraicClosure ℚ) (WithConv.ofConv (1 : WithConv (CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ))) fun φ => ?_
    show (1 : WithConv (CartierDual ↥O H₀ →ₐ[↥O] AlgebraicClosure ℚ)) φ = algebraMap ↥O (AlgebraicClosure ℚ) (φ 1)
    rw [AlgHom.convOne_apply]
    exact congrArg (algebraMap ↥O (AlgebraicClosure ℚ)) (CartierDual.counit_apply φ)
  have hE'pow_val : ∀ y (k : ℕ), (E' (y ^ k)).val = (E' y).val ^ k := by
    intro y k
    induction k with
    | zero => rw [pow_zero, pow_zero, hE'one_val]
    | succ k ih => rw [pow_succ, pow_succ, hE'mul_val, ih]
  have hE'inj : Function.Injective E' := fun y z h =>
    WithConv.ofConv_injective ((e (AlgebraicClosure ℚ)).injective h)
  have h1 : (E' (Φ x)).val ^ q = 1 :=
    groupLike_pow_eq_one q O hOdvr H₀ a hrank hpts hptq _ (E' (Φ x)).isGroupLikeElem_val
  have h2 : (E' ((Φ x) ^ q)).val = (E' 1).val := by rw [hE'pow_val, h1, hE'one_val]
  have h3 : (Φ x) ^ q = 1 := hE'inj (GroupLike.val_injective h2)
  apply hΦinj
  rw [hΦpow, h3, hΦone]

private theorem cartierDual_points_residue_comp_ne
    (q : ℕ) [Fact q.Prime]
    (O : Subring (AlgebraicClosure ℚ))
    (hOdvr : IsDiscreteValuationRing ↥O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀] [Coalgebra.IsCocomm ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (hq2 : q ≠ 2) (hOirr : Irreducible ((q : ℕ) : ↥O))
    (x x' : WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O)) (hne : x ≠ x') :
    (IsLocalRing.residue ↥O).comp (WithConv.ofConv x).toRingHom
      ≠ (IsLocalRing.residue ↥O).comp (WithConv.ofConv x').toRingHom := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  intro hres
  apply hne
  let κ := IsLocalRing.ResidueField ↥O
  let r : ↥O →ₐ[↥O] κ := Algebra.ofId ↥O κ
  let R : WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O) → WithConv (CartierDual ↥O H₀ →ₐ[↥O] κ) :=
    fun y => WithConv.toConv (r.comp (WithConv.ofConv y))
  have hRmul : ∀ y z, R (y * z) = R y * R z := by
    intro y z
    show WithConv.toConv (r.comp (WithConv.ofConv (y * z))) = _
    rw [AlgHom.comp_convMul_distrib]
  have hRpow : ∀ y (k : ℕ), R (y ^ (k + 1)) = R y * R (y ^ k) := by
    intro y k
    rw [pow_succ', hRmul]
  have hRx : R x = R x' := by
    apply WithConv.ext
    apply AlgHom.ext
    intro φ
    have := DFunLike.congr_fun hres φ
    exact this
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_ne_zero hq0).symm⟩
  let w : WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O) := x * x' ^ k
  have hx'q : x' ^ q = 1 := cartierDual_point_pow_eq_one q O hOdvr H₀ a hrank hpts hptq x'
  have hRw : R w = R 1 := by
    show R (x * x' ^ k) = R 1
    rw [hRmul, hRx, ← hRpow, ← hk, hx'q]
  have hw1 : ∀ φ : CartierDual ↥O H₀,
      w φ - algebraMap ↥O ↥O (Coalgebra.counit φ) ∈ IsLocalRing.maximalIdeal ↥O := by
    intro φ
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    have h1 := congrArg (fun g : WithConv (CartierDual ↥O H₀ →ₐ[↥O] κ) => g φ) hRw
    have h2 : (R 1) φ = IsLocalRing.residue ↥O (algebraMap ↥O ↥O (Coalgebra.counit φ)) := by
      show algebraMap ↥O κ ((1 : WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O)) φ) = _
      rw [AlgHom.convOne_apply]
      rfl
    exact h1.trans h2
  have hwq : w ^ q = 1 := cartierDual_point_pow_eq_one q O hOdvr H₀ a hrank hpts hptq w
  have hw : w = 1 :=
    HopfAlgebra.point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal (↥O) q hq2 hOirr (CartierDual ↥O H₀)
      w hw1 q (Nat.pos_of_ne_zero hq0) hwq
  calc x = x * x' ^ q := by rw [hx'q, mul_one]
    _ = (x * x' ^ k) * x' := by rw [hk, pow_succ, mul_assoc]
    _ = x' := by
        show w * x' = x'
        rw [hw, one_mul]

private theorem cartierDual_eval_bijective
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀] [Coalgebra.IsCocomm ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (hq2 : q ≠ 2) (hOirr : Irreducible ((q : ℕ) : ↥O)) :
    Function.Bijective (fun (a : CartierDual ↥O H₀) (x : WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O)) =>
      (WithConv.ofConv x) a) := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  let ι := WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O)
  have hιcard : Nat.card ι = q ^ a := by
    rw [← natCard_cartierDual_algHom_eq q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ]
    exact Nat.card_congr ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite ι := Nat.finite_of_card_ne_zero (hιcard ▸ pow_ne_zero a hq0)
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank ↥O (CartierDual ↥O H₀) := by
    rw [Fintype.card_eq_nat_card, hιcard, CartierDual.finrank_eq, hrank]
  exact eval_bijective_of_card_eq_finrank_of_residue_comp_ne (O := ↥O) (B := CartierDual ↥O H₀)
    (fun x : ι => WithConv.ofConv x) hcard
    (fun i j hij => cartierDual_points_residue_comp_ne q O hOdvr H₀ a hrank hpts hptq hq2 hOirr i j hij)

private theorem nonempty_linearEquiv_pi_zmod_of_natCard (q : ℕ) [Fact q.Prime] (V : Type) [AddCommGroup V] [Module (ZMod q) V] [Finite V]
    (a : ℕ) (hcard : Nat.card V = q ^ a) : Nonempty (V ≃ₗ[ZMod q] (Fin a → ZMod q)) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Module.Finite (ZMod q) V := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod q) V = a := by
    have h := Module.card_eq_pow_finrank (K := ZMod q) (V := V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
    exact (Nat.pow_right_injective (Fact.out : q.Prime).two_le h).symm
  have hfr' : Module.finrank (ZMod q) V = Module.finrank (ZMod q) (Fin a → ZMod q) := by
    rw [hfr, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact ⟨LinearEquiv.ofFinrankEq (R := ZMod q) V (Fin a → ZMod q) hfr'⟩

private theorem exists_bialgEquiv_monoidAlgebra_of_chiType
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra ↥O H₀]
    [Module.Finite ↥O H₀] [Module.Flat ↥O H₀] [Coalgebra.IsCocomm ↥O H₀]
    (a : ℕ) (hrank : Module.finrank ↥O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[↥O] AlgebraicClosure ℚ), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (hq2 : q ≠ 2) (hOirr : Irreducible ((q : ℕ) : ↥O)) :
    Nonempty (H₀ ≃ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))) := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  let Γ := WithConv (CartierDual ↥O H₀ →ₐ[↥O] ↥O)
  have hΓcard : Nat.card Γ = q ^ a := by
    rw [← natCard_cartierDual_algHom_eq q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ]
    exact Nat.card_congr ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite Γ := Nat.finite_of_card_ne_zero (hΓcard ▸ pow_ne_zero a hq0)
  obtain ⟨ψ, -⟩ := CartierDual.exists_bialgEquiv_monoidAlgebra_of_points (↥O) (CartierDual ↥O H₀) Γ (MonoidHom.id Γ)
    (cartierDual_eval_bijective q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ hq2 hOirr)
  obtain ⟨e₁, -⟩ := CartierDual.exists_bialgEquiv_bidual (↥O) H₀
  obtain ⟨e₂, -⟩ := CartierDual.exists_bialgEquiv_bidual (↥O) (MonoidAlgebra ↥O Γ)
  let e₃ : CartierDual ↥O (CartierDual ↥O H₀) ≃ₐc[↥O] CartierDual ↥O (CartierDual ↥O (MonoidAlgebra ↥O Γ)) :=
    (CartierDual.congr ψ).symm
  let eΓ : H₀ ≃ₐc[↥O] MonoidAlgebra ↥O Γ := e₁.trans (e₃.trans e₂.symm)
  have hpowq : ∀ x : Γ, x ^ q = 1 := fun x =>
    cartierDual_point_pow_eq_one q O hOdvr H₀ a hrank hpts hptq x
  have hunit : ∀ x : Γ, IsUnit x := fun x => IsUnit.of_pow_eq_one (hpowq x) hq0
  letI : CommGroup Γ := { groupOfIsUnit hunit with mul_comm := mul_comm }
  have hpowq' : ∀ g : Γ, g ^ q = 1 := fun g => hpowq g
  have hexpA : ∀ v : Additive Γ, q • v = 0 := by
    intro v
    have h := congrArg Additive.ofMul (hpowq' (Additive.toMul v))
    rwa [ofMul_pow, ofMul_toMul, ofMul_one] at h
  have hcardA : Nat.card (Additive Γ) = q ^ a := (Nat.card_congr Additive.toMul).trans hΓcard
  haveI : Module (ZMod q) (Additive Γ) := AddCommGroup.zmodModule hexpA
  obtain ⟨fL⟩ := nonempty_linearEquiv_pi_zmod_of_natCard q (Additive Γ) a hcardA
  let f : Γ ≃* Multiplicative (Fin a → ZMod q) := AddEquiv.toMultiplicativeRight fL.toAddEquiv
  let fh : Γ →* Multiplicative (Fin a → ZMod q) := f.toMonoidHom
  let gh : Multiplicative (Fin a → ZMod q) →* Γ := f.symm.toMonoidHom
  have hfg : fh.comp gh = MonoidHom.id _ := MonoidHom.ext fun z => f.apply_symm_apply z
  have hgf : gh.comp fh = MonoidHom.id _ := MonoidHom.ext fun x => f.symm_apply_apply x
  let eZ : MonoidAlgebra ↥O Γ ≃ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) :=
    BialgEquiv.ofBialgHom (MonoidAlgebra.mapDomainBialgHom ↥O fh) (MonoidAlgebra.mapDomainBialgHom ↥O gh)
      (by rw [← MonoidAlgebra.mapDomainBialgHom_comp, hfg, MonoidAlgebra.mapDomainBialgHom_id])
      (by rw [← MonoidAlgebra.mapDomainBialgHom_comp, hgf, MonoidAlgebra.mapDomainBialgHom_id])
  exact ⟨eΓ.trans eZ⟩

private theorem exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub_of_finite
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (hq2 : q ≠ 2) (hOirr : Irreducible ((q : ℕ) : ↥O))
    (HO : Type) [CommRing HO] [HopfAlgebra ↥O HO]
    [Module.Finite ↥O HO] [Module.Flat ↥O HO] [Coalgebra.IsCocomm ↥O HO]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M S : AddSubgroup J) (hSM : S ≤ M) (hMfin : Finite ↥M)
    (pts : WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M)
    (hadd : ∀ f g, pts (f * g) = pts f + pts g)
    (hact : ∀ σ (_ : σ ∈ A.inertiaSubgroupIn ℚ)
      (f g : WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ)),
      (∀ x : HO, g x = σ (f x)) → ((pts g : ↥M) : J) = σ • ((pts f : ↥M) : J))
    (a : ℕ) (hcardS : Nat.card ↥S = q ^ a)
    (hS : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) → ∀ x ∈ S, σ • x = c • x) :
    ∃ p₀ : HO →ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p₀ ∧
      ∀ f : HO →ₐ[↥O] AlgebraicClosure ℚ,
        (∃ g : MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) →ₐ[↥O] AlgebraicClosure ℚ,
            g.comp (p₀ : HO →ₐ[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))) = f) ↔
          ((pts (WithConv.toConv f) : ↥M) : J) ∈ S := by
  classical
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Finite ↥M := hMfin
  have hqp : q.Prime := Fact.out
  have hq0 : q ≠ 0 := hqp.ne_zero
  have htorsS : ∀ x ∈ S, q • x = 0 := by
    intro x hx
    have h := hS 1 (Subgroup.one_mem _) (q + 1)
      (fun ζ hζ => by rw [AlgEquiv.one_apply, pow_succ, hζ, one_mul]) x hx
    rw [one_smul, add_nsmul, one_nsmul] at h
    have h' : 0 + x = q • x + x := by rwa [zero_add]
    exact (add_right_cancel h').symm
  have hpts1 : pts 1 = 0 := by
    have h := hadd 1 1
    rw [one_mul] at h
    have h' : pts 1 + pts 1 = pts 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hpow : ∀ (f : WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ)) (k : ℕ), pts (f ^ k) = k • pts f := by
    intro f k
    induction k with
    | zero => rw [pow_zero, zero_nsmul, hpts1]
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  have hptsS : ∀ f : WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ), ((pts f : ↥M) : J) ∈ S → f ^ q = 1 := by
    intro f hf
    apply pts.injective
    rw [hpow, hpts1]
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]
    exact htorsS _ hf
  have hτ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∃ τ : AlgebraicClosure ℚ →ₐ[↥O] AlgebraicClosure ℚ, ∀ z, τ z = σ z :=
    fun σ hσ => ⟨{ (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) with
      commutes' := fun o => (hOfix σ).mp hσ o o.2 }, fun _ => rfl⟩
  let act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ↥M → ↥M := fun σ x =>
    if hσ : σ ∈ A.inertiaSubgroupIn ℚ then
      pts (WithConv.toConv ((hτ σ hσ).choose.comp (WithConv.ofConv (pts.symm x))))
    else x
  have act_def : ∀ σ x, act σ x =
      if hσ : σ ∈ A.inertiaSubgroupIn ℚ then
        pts (WithConv.toConv ((hτ σ hσ).choose.comp (WithConv.ofConv (pts.symm x))))
      else x := fun _ _ => rfl
  have hact_of_mem : ∀ σ (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : ↥M), ((act σ x : ↥M) : J) = σ • (x : J) := by
    intro σ hσ x
    rw [act_def, dif_pos hσ]
    have h := hact σ hσ (pts.symm x)
      (WithConv.toConv ((hτ σ hσ).choose.comp (WithConv.ofConv (pts.symm x))))
      (fun y => (hτ σ hσ).choose_spec ((WithConv.ofConv (pts.symm x)) y))
    rw [Equiv.apply_symm_apply] at h
    exact h
  have hact_of_not_mem : ∀ σ, σ ∉ A.inertiaSubgroupIn ℚ → ∀ x, act σ x = x := fun σ hσ x => by
    rw [act_def, dif_neg hσ]
  have hrow_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ)),
      (∀ h : HO, g h = σ (f h)) → pts g = act σ (pts f) := by
    intro σ f g hfg
    have hσ : σ ∈ A.inertiaSubgroupIn ℚ := by
      rw [hOfix]
      intro o ho
      have h1 : σ ((WithConv.ofConv f) (algebraMap ↥O HO ⟨o, ho⟩)) = (WithConv.ofConv g) (algebraMap ↥O HO ⟨o, ho⟩) :=
        (hfg _).symm
      rw [(WithConv.ofConv f).commutes ⟨o, ho⟩, (WithConv.ofConv g).commutes ⟨o, ho⟩] at h1
      exact h1
    rw [act_def, dif_pos hσ, Equiv.symm_apply_apply]
    congr 1
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    exact (hfg h).trans ((hτ σ hσ).choose_spec (f h)).symm
  let N : Fin (1 + 1) → AddSubgroup ↥M := fun i => if (i : ℕ) = 0 then S.addSubgroupOf M else ⊤
  have hN : ∀ i, N i = if (i : ℕ) = 0 then S.addSubgroupOf M else ⊤ := fun _ => rfl
  have h0 : ((0 : Fin (1 + 1)) : ℕ) = 0 := rfl
  have hmono : ∀ i : Fin 1, N i.castSucc ≤ N i.succ := by
    intro i
    have h1 : ((i.succ : Fin (1 + 1)) : ℕ) ≠ 0 := by rw [Fin.val_succ]; exact Nat.succ_ne_zero _
    rw [hN i.succ, if_neg h1]
    exact le_top
  have htop : N (Fin.last 1) = ⊤ := by
    rw [hN, if_neg (show ((Fin.last 1 : Fin (1 + 1)) : ℕ) ≠ 0 by decide)]
  have hstab : ∀ (i : Fin (1 + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥M),
      x ∈ N i → act σ x ∈ N i := by
    intro i σ x hx
    rw [hN] at hx ⊢
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi] at hx ⊢
      rw [AddSubgroup.mem_addSubgroupOf] at hx ⊢
      by_cases hσ : σ ∈ A.inertiaSubgroupIn ℚ
      · rw [hact_of_mem σ hσ x]
        obtain ⟨c, hc⟩ := AlgebraicClosure.exists_apply_eq_pow_of_pow_eq_one q hq0 σ
        rw [hS σ hσ c hc _ hx]
        exact S.nsmul_mem hx c
      · rw [hact_of_not_mem σ hσ x]
        exact hx
    · rw [if_neg hi] at hx ⊢
      exact AddSubgroup.mem_top _
  obtain ⟨B, instCR, instHA, π, -, -, hflat, hπsurj, -, -, -, hfactor, hcocomm, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain (↥O)
      (fun x y (h : algebraMap ↥O (AlgebraicClosure ℚ) x = algebraMap ↥O (AlgebraicClosure ℚ) y) => Subtype.ext h)
      HO (↥M) pts hadd act hrow_act 1 N hmono htop hstab
  haveI : Module.Flat ↥O (B 0) := hflat 0
  haveI : Module.Finite ↥O (B 0) := (hfin inferInstance 0).1
  haveI : Coalgebra.IsCocomm ↥O (B 0) := hcocomm inferInstance 0
  let π₀ : HO →ₐc[↥O] B 0 := π 0
  have hrank : Module.finrank ↥O (B 0) = q ^ a := by
    rw [(hfin inferInstance 0).2 (by decide), hN, if_pos h0, ← hcardS]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hSM).toEquiv
  have hfac0 : ∀ f : HO →ₐ[↥O] AlgebraicClosure ℚ,
      (∃ g : B 0 →ₐ[↥O] AlgebraicClosure ℚ, g.comp (π₀ : HO →ₐ[↥O] B 0) = f) ↔
        ((pts (WithConv.toConv f) : ↥M) : J) ∈ S := by
    intro f
    rw [hfactor 0 f, hN, if_pos h0, AddSubgroup.mem_addSubgroupOf]
  have hcomp_inj : ∀ g₁ g₂ : B 0 →ₐ[↥O] AlgebraicClosure ℚ,
      g₁.comp (π₀ : HO →ₐ[↥O] B 0) = g₂.comp (π₀ : HO →ₐ[↥O] B 0) → g₁ = g₂ := by
    intro g₁ g₂ h
    refine AlgHom.ext fun b => ?_
    obtain ⟨x, rfl⟩ := hπsurj 0 b
    exact DFunLike.congr_fun h x
  have hpts_comp : ∀ (g : WithConv (B 0 →ₐ[↥O] AlgebraicClosure ℚ)) (k : ℕ),
      (WithConv.ofConv (g ^ k)).comp (π₀ : HO →ₐ[↥O] B 0)
        = WithConv.ofConv ((WithConv.toConv ((WithConv.ofConv g).comp (π₀ : HO →ₐ[↥O] B 0))) ^ k) := by
    intro g k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero]
        refine AlgHom.ext fun x => ?_
        change algebraMap ↥O (AlgebraicClosure ℚ) (Coalgebra.counit (π₀ x))
          = algebraMap ↥O (AlgebraicClosure ℚ) (Coalgebra.counit x)
        rw [CoalgHomClass.counit_comp_apply]
    | succ k ih =>
        rw [pow_succ, pow_succ, AlgHom.convMul_comp_bialgHom_distrib, ih, WithConv.toConv_ofConv]
  have hpts0 : Nat.card (WithConv (B 0 →ₐ[↥O] AlgebraicClosure ℚ)) = q ^ a := by
    rw [Nat.card_congr (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ :
      WithConv (B 0 →ₐ[↥O] AlgebraicClosure ℚ) ≃ (B 0 →ₐ[↥O] AlgebraicClosure ℚ))]
    rw [← hcardS, ← Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hSM).toEquiv]
    apply Nat.card_eq_of_bijective
      (fun g : B 0 →ₐ[↥O] AlgebraicClosure ℚ =>
        (⟨pts (WithConv.toConv (g.comp (π₀ : HO →ₐ[↥O] B 0))),
          AddSubgroup.mem_addSubgroupOf.mpr ((hfac0 _).mp ⟨g, rfl⟩)⟩ : ↥(S.addSubgroupOf M)))
    constructor
    · intro g₁ g₂ h
      have h1 := congrArg Subtype.val h
      exact hcomp_inj _ _ (WithConv.toConv_injective (pts.injective h1))
    · rintro ⟨x, hx⟩
      rw [AddSubgroup.mem_addSubgroupOf] at hx
      obtain ⟨g, hg⟩ := (hfac0 (WithConv.ofConv (pts.symm x))).mpr
        (by rwa [WithConv.toConv_ofConv, Equiv.apply_symm_apply])
      refine ⟨g, Subtype.ext ?_⟩
      simp only [hg, WithConv.toConv_ofConv, Equiv.apply_symm_apply]
  have hptq : ∀ g : WithConv (B 0 →ₐ[↥O] AlgebraicClosure ℚ), g ^ q = 1 := by
    intro g
    have hg : (WithConv.toConv ((WithConv.ofConv g).comp (π₀ : HO →ₐ[↥O] B 0))) ^ q = 1 :=
      hptsS _ ((hfac0 _).mp ⟨WithConv.ofConv g, rfl⟩)
    apply WithConv.ofConv_injective
    apply hcomp_inj
    rw [hpts_comp, hg]
    have hz := hpts_comp g 0
    rw [pow_zero, pow_zero] at hz
    exact hz.symm
  have hχ0 : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (B 0 →ₐ[↥O] AlgebraicClosure ℚ), (∀ b : B 0, g b = σ (f b)) → g = f ^ c := by
    intro σ hσ c hc f g hfg
    let f' : WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ) :=
      WithConv.toConv ((WithConv.ofConv f).comp (π₀ : HO →ₐ[↥O] B 0))
    let g' : WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ) :=
      WithConv.toConv ((WithConv.ofConv g).comp (π₀ : HO →ₐ[↥O] B 0))
    have hf'g' : ∀ x : HO, g' x = σ (f' x) := fun x => hfg (π₀ x)
    have hmemf : ((pts f' : ↥M) : J) ∈ S := (hfac0 _).mp ⟨WithConv.ofConv f, rfl⟩
    have h1 : ((pts g' : ↥M) : J) = σ • ((pts f' : ↥M) : J) := hact σ hσ f' g' hf'g'
    rw [hS σ hσ c hc _ hmemf] at h1
    have h2 : pts g' = pts (f' ^ c) := by
      rw [hpow]
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_nsmul]
      exact h1
    have h3 : g' = f' ^ c := pts.injective h2
    apply WithConv.ofConv_injective
    apply hcomp_inj
    rw [hpts_comp]
    change WithConv.ofConv g' = WithConv.ofConv (f' ^ c)
    rw [h3]
  obtain ⟨eB⟩ := exists_bialgEquiv_monoidAlgebra_of_chiType q A O hOA hOdvr hOfix hOmax (B 0) a hrank hpts0 hptq hχ0 hq2 hOirr
  let p₀ : HO →ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) := eB.toBialgHom.comp π₀
  refine ⟨p₀, (EquivLike.surjective eB).comp (hπsurj 0), fun f => ?_⟩
  rw [← hfac0 f]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.comp (eB.toBialgHom : B 0 →ₐ[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))), ?_⟩
    rw [← hg]
    exact AlgHom.ext fun x => rfl
  · rintro ⟨g, hg⟩
    refine ⟨g.comp (eB.symm.toBialgHom : MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) →ₐ[↥O] B 0), ?_⟩
    rw [← hg]
    refine AlgHom.ext fun x => ?_
    change g (eB.symm (eB (π₀ x))) = g (π₀ x)
    congr 1
    exact eB.toEquiv.symm_apply_apply (π₀ x)

private theorem exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub'
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOirr : Irreducible ((q : ℕ) : ↥O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H : Type) [CommRing H] [HopfAlgebra ↥O H]
    [Module.Finite ↥O H] [Module.Flat ↥O H] [Coalgebra.IsCocomm ↥O H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M S : AddSubgroup J) (hSM : S ≤ M)
    (pts : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M)
    (hadd : ∀ f g, pts (f * g) = pts f + pts g)
    (hact : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ),
      (∀ x : H, g x = σ (f x)) → ((pts g : ↥M) : J) = σ • ((pts f : ↥M) : J))
    (a : ℕ) (hcardS : Nat.card ↥S = q ^ a)
    (hS : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) → ∀ x ∈ S, σ • x = c • x) :
    ∃ p : H →ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p ∧
      ∀ f : H →ₐ[↥O] AlgebraicClosure ℚ,
        (∃ g : MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) →ₐ[↥O] AlgebraicClosure ℚ,
            g.comp (p : H →ₐ[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))) = f) ↔
          ((pts (WithConv.toConv f) : ↥M) : J) ∈ S := by
  haveI : IsDiscreteValuationRing ↥O := hOdvr
  haveI : Module.Free ↥O H := Module.free_of_flat_of_isLocalRing
  let f₀ : H →ₐ[↥O] AlgebraicClosure ℚ := WithConv.ofConv (pts.symm ⟨0, M.zero_mem⟩)
  haveI : Nontrivial H := ⟨⟨1, 0, fun h => one_ne_zero (by rw [← map_one f₀, h, map_zero])⟩⟩
  have hcard : Nat.card (H →ₐ[↥O] AlgebraicClosure ℚ) = Module.finrank ↥O H :=
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ↥O H (AlgebraicClosure ℚ)
  haveI : Finite (H →ₐ[↥O] AlgebraicClosure ℚ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact ((Module.finrank_pos_iff_of_free (R := ↥O) H).mpr inferInstance).ne')
  haveI : Finite ↥M :=
    Finite.of_surjective (fun f : H →ₐ[↥O] AlgebraicClosure ℚ => pts (WithConv.toConv f))
      (fun m => ⟨WithConv.ofConv (pts.symm m), by simp⟩)
  exact exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub_of_finite q A O hOA hOdvr hOfix hOmax hq2 hOirr H M S hSM
    inferInstance pts hadd (fun σ hσ f g h => hact σ hσ f g h) a hcardS hS

end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub.HopfPoints"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOirr : Irreducible ((q : ℕ) : ↥O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H : Type) [CommRing H] [HopfAlgebra ↥O H]
    [Module.Finite ↥O H] [Module.Flat ↥O H] [Coalgebra.IsCocomm ↥O H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M S : AddSubgroup J) (hSM : S ≤ M)
    (pts : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M)
    (hadd : ∀ f g, pts (f * g) = pts f + pts g)
    (hact : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ),
      (∀ x : H, g x = σ (f x)) → ((pts g : ↥M) : J) = σ • ((pts f : ↥M) : J))
    (a : ℕ) (hcardS : Nat.card ↥S = q ^ a)
    (hS : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) → ∀ x ∈ S, σ • x = c • x) :
    ∃ p : H →ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p ∧
      ∀ f : H →ₐ[↥O] AlgebraicClosure ℚ,
        (∃ g : MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) →ₐ[↥O] AlgebraicClosure ℚ,
            g.comp (p : H →ₐ[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))) = f) ↔
          ((pts (WithConv.toConv f) : ↥M) : J) ∈ S :=
  HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub' q hq2 A O hOA hOdvr hOirr hOfix
    hOmax H M S hSM pts hadd hact a hcardS hS

end
p2m_reactivate "P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub.HopfPoints"

end S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
end P2MW
export P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub (solution)
