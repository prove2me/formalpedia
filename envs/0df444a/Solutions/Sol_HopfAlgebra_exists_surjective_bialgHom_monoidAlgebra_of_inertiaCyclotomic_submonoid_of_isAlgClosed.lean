-- Prove2me | solution 1 for HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c788b34c-bd92-59b1-b9b8-96cdb5ec3c9c

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_HopfAlgebra_exists_comp_antipode_convMul_eq_one
import Theorems.Thm_CartierDual_exists_algHomEquiv_groupLike
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

universe u v w

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

theorem S17.SurjMonAlgGen.exists_apply_eq_pow_of_pow_eq_one
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (n : ℕ) (hn : n ≠ 0) (σ : L ≃ₐ[K] L) :
    ∃ a : ℕ, ∀ μ : L, μ ^ n = 1 → σ μ = μ ^ a := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨m, hm⟩ := rootsOfUnity.integer_power_of_ringEquiv' n σ.toRingEquiv
  refine ⟨(m % (n : ℤ)).toNat, fun μ hμ => ?_⟩
  let t : Lˣ := Units.ofPowEqOne μ n hμ hn
  have htL : (t : L) = μ := rfl
  have htmem : t ∈ rootsOfUnity n L := by
    rw [mem_rootsOfUnity']
    exact hμ
  have htn : t ^ n = 1 := (mem_rootsOfUnity n t).mp htmem
  have hk : (((m % (n : ℤ)).toNat : ℕ) : ℤ) = m % (n : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hn))
  have h2 : t ^ m = t ^ (m % (n : ℤ)).toNat := by
    rw [zpow_eq_zpow_emod' m htn, ← zpow_natCast, hk]
  have h1 : σ.toRingEquiv (t : L) = ((t ^ m : Lˣ) : L) := hm t htmem
  rw [h2, Units.val_pow_eq_pow_val, htL] at h1
  exact h1

theorem S17.SurjMonAlgGen.fixedPoints_of_inertia
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (O : Type) [CommRing O] [Algebra O L]
    (hOfix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O L x) = algebraMap O L x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn K, σ y = y) → ∃ x : O, algebraMap O L x = y) :
    ∀ c : L, (∀ σ : L ≃ₐ[K] L, (∀ r : O, σ (algebraMap O L r) = algebraMap O L r) → σ c = c) →
      ∃ a b : O, algebraMap O L b ≠ 0 ∧ c * algebraMap O L b = algebraMap O L a := by
  intro c hc
  have hcfix : ∀ σ ∈ A.inertiaSubgroupIn K, σ c = c := fun σ hσ => hc σ ((hOfix σ).mp hσ)
  by_cases hcA : c ∈ A
  · obtain ⟨x, hx⟩ := hOmax c hcA hcfix
    refine ⟨x, 1, ?_, ?_⟩
    · rw [map_one]; exact one_ne_zero
    · rw [map_one, mul_one, hx]
  · have hc0 : c ≠ 0 := by
      rintro rfl
      exact hcA A.zero_mem
    have hinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hinvfix : ∀ σ ∈ A.inertiaSubgroupIn K, σ c⁻¹ = c⁻¹ := fun σ hσ => by
      rw [map_inv₀, hcfix σ hσ]
    obtain ⟨x, hx⟩ := hOmax c⁻¹ hinv hinvfix
    refine ⟨1, x, ?_, ?_⟩
    · rw [hx]; exact inv_ne_zero hc0
    · rw [hx, map_one, mul_inv_cancel₀ hc0]

namespace HopfPoints

theorem eval_bijective_of_card_eq_finrank_of_residue_comp_ne
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

noncomputable def evalAt (p : H →ₐ[O] L) : L ⊗[O] H →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) p (fun _ _ => Commute.all _ _)

@[scoped simp] theorem evalAt_tmul (p : H →ₐ[O] L) (c : L) (h : H) : evalAt p (c ⊗ₜ h) = c * p h := by
  simp [evalAt]

theorem evalAt_map_twist (τ : L →ₐ[O] L) (p p' : H →ₐ[O] L) (hpp' : ∀ h, p h = τ (p' h)) (x : L ⊗[O] H) :
    evalAt p (Algebra.TensorProduct.map τ (AlgHom.id O H) x) = τ (evalAt p' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c h => simp [hpp', map_mul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem evalAt_convMul (p p' : WithConv (H →ₐ[O] L)) (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
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

theorem evalAt_one (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
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

theorem evalAt_pow (p : WithConv (H →ₐ[O] L)) (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) (k : ℕ) :
    evalAt (WithConv.ofConv (p ^ k)) x = (evalAt (WithConv.ofConv p) x) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, evalAt_one x hx]
  | succ k ih => rw [pow_succ, pow_succ, evalAt_convMul _ _ x hx, ih]

theorem eval_injective [Nontrivial O] [Module.Finite O H] [Module.Free O H]
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

theorem map_twist_eq_self_of_isGroupLikeElem [Nontrivial O] [Module.Finite O H] [Module.Free O H]
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
p2m_reactivate "P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed.HopfPoints"

namespace AlgHom p2m_export "AlgHom" "comp_convMul_distrib ext toLinearMap_apply commutes toLinearMap one_apply convOne_apply coe_toRingHom toLinearMap_convMul comp mk toRingHom toRingHom_eq_coe card mem_range_self range_eq_top Finite commutes' coe_comp convMul_comp_bialgHom_distrib comp_apply convMul_apply mem_range" end AlgHom
p2m_open_scoped "AlgHom" in
theorem AlgHom.apply_mem_valuationSubring_of_moduleFinite
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (H₁ : Type) [CommRing H₁] [Algebra O H₁] [Module.Finite O H₁]
    (f : H₁ →ₐ[O] L) (h : H₁) : f h ∈ A := by
  classical
  have hint : IsIntegral O (f h) := (Algebra.IsIntegral.isIntegral (R := O) h).map f
  obtain ⟨p, hpm, hpev⟩ := hint
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : A.valuation (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap O L (p.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpev
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree, algebraMap O L (p.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : A.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap O L (p.coeff i) * f h ^ i) < A.valuation (f h) ^ p.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (algebraMap O L (p.coeff i)) * A.valuation (f h) ^ i
        ≤ 1 * A.valuation (f h) ^ i := by
          exact mul_le_mul' ((A.valuation_le_one_iff _).mpr (hOA (p.coeff i))) le_rfl
      _ = A.valuation (f h) ^ i := one_mul _
      _ < A.valuation (f h) ^ p.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : A.valuation (f h ^ p.natDegree) < A.valuation (f h) ^ p.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk exists_comp_antipode_convMul_eq_one natCard_algHom_eq_finrank_of_charZero point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal exists_quotientFlag_of_galoisStableChain_of_fixedPoints"
p2m_open "HopfAlgebra"

open HopfPoints

theorem groupLike_pow_eq_one
    (q : ℕ) [Fact q.Prime]
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOdvr : IsDiscreteValuationRing O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (x : TensorProduct O L H₀) (hx : IsGroupLikeElem L x) :
    x ^ q = 1 := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  let ι := H₀ →ₐ[O] L
  have hιcard : Nat.card ι = q ^ a := by
    rw [← hpts]
    exact Nat.card_congr ⟨WithConv.toConv, WithConv.ofConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite ι := Nat.finite_of_card_ne_zero (hιcard ▸ pow_ne_zero a hq0)
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank O H₀ := by
    rw [Fintype.card_eq_nat_card, hιcard, hrank]
  refine eval_injective (fun f : ι => f) (fun _ _ h => h) hcard _ _ fun p => ?_
  rw [map_pow, map_one]
  have h1 := evalAt_pow (WithConv.toConv p) x hx q
  rw [hptq (WithConv.toConv p), WithConv.ofConv_toConv, evalAt_one x hx] at h1
  exact h1.symm

theorem cartierDual_point_apply_fixed
    (q : ℕ) [Fact q.Prime]
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOdvr : IsDiscreteValuationRing O)
    (hOfix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O L x) = algebraMap O L x)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀] [Coalgebra.IsCocomm O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[O] L), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (ψ : CartierDual O H₀ →ₐ[O] L) (φ : CartierDual O H₀) :
    σ (ψ φ) = ψ φ := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hσ' : σ⁻¹ ∈ A.inertiaSubgroupIn K := Subgroup.inv_mem _ hσ
  let τ : L →ₐ[O] L :=
    { (σ : L →+* L) with
      commutes' := fun o => (hOfix σ).mp hσ o }
  let τ' : L →ₐ[O] L :=
    { ((σ⁻¹ : L ≃ₐ[K] L) : L →+* L) with
      commutes' := fun o => (hOfix σ⁻¹).mp hσ' o }
  have hτ : ∀ z, τ z = σ z := fun _ => rfl
  have hτ' : ∀ z, τ' z = σ⁻¹ z := fun _ => rfl
  have hττ' : ∀ z, τ (τ' z) = z := by
    intro z
    rw [hτ, hτ', AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  obtain ⟨c', hc'⟩ := S17.SurjMonAlgGen.exists_apply_eq_pow_of_pow_eq_one q hq0 σ⁻¹
  have hτ'ζ : ∀ ζ : L, ζ ^ q = 1 → τ' ζ = ζ ^ c' := fun ζ hζ => by
    rw [hτ']; exact hc' ζ hζ
  have hτ'pts : ∀ f : WithConv (H₀ →ₐ[O] L),
      WithConv.toConv (τ'.comp (WithConv.ofConv f)) = f ^ c' :=
    fun f => hχ σ⁻¹ hσ' c' hc' f _ (fun _ => rfl)
  let ι := H₀ →ₐ[O] L
  have hιcard : Nat.card ι = q ^ a := by
    rw [← hpts]
    exact Nat.card_congr ⟨WithConv.toConv, WithConv.ofConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite ι := Nat.finite_of_card_ne_zero (hιcard ▸ pow_ne_zero a hq0)
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank O H₀ := by
    rw [Fintype.card_eq_nat_card, hιcard, hrank]
  obtain ⟨e, _he1, _he2, _he3, he4⟩ := CartierDual.exists_algHomEquiv_groupLike (O) H₀
  have hm : ∀ x : TensorProduct O L H₀, IsGroupLikeElem L x → x ^ q = 1 :=
    fun x hx => groupLike_pow_eq_one q O hOdvr H₀ a hrank hpts hptq x hx
  have hfix : Algebra.TensorProduct.map τ (AlgHom.id O H₀) (e L ψ).val
      = (e L ψ).val :=
    map_twist_eq_self_of_isGroupLikeElem (fun f : ι => f) (fun _ _ h => h) hcard q hm τ τ' hττ' c' hτ'ζ hτ'pts
      _ (e L ψ).isGroupLikeElem_val
  have hnat := he4 L L τ ψ
  rw [hfix] at hnat
  have heq : e L (τ.comp ψ) = e L ψ := GroupLike.val_injective hnat
  have hψ : τ.comp ψ = ψ := (e L).injective heq
  have := DFunLike.congr_fun hψ φ
  rw [AlgHom.comp_apply, hτ] at this
  exact this

theorem cartierDual_point_factors
    (q : ℕ) [Fact q.Prime]
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O)
    (hOfix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O L x) = algebraMap O L x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn K, σ y = y) → ∃ x : O, algebraMap O L x = y)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀] [Coalgebra.IsCocomm O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[O] L), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (ψ : CartierDual O H₀ →ₐ[O] L) :
    ∃ ψO : CartierDual O H₀ →ₐ[O] O, ∀ φ, algebraMap O L (ψO φ) = ψ φ := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  have hψO : ∀ φ, ∃ x : O, algebraMap O L x = ψ φ := fun φ =>
    hOmax _ (AlgHom.apply_mem_valuationSubring_of_moduleFinite A O hOA (CartierDual O H₀) ψ φ)
      (fun σ hσ => cartierDual_point_apply_fixed q A O hOdvr hOfix H₀ a hrank hpts hptq hχ σ hσ ψ φ)
  choose x hx using hψO
  have hinjO : Function.Injective (algebraMap O L) := FaithfulSMul.algebraMap_injective O _
  refine ⟨{ toFun := x
            map_one' := hinjO (by rw [hx, map_one, map_one])
            map_mul' := fun a b => hinjO (by rw [hx, map_mul, map_mul, hx, hx])
            map_zero' := hinjO (by rw [hx, map_zero, map_zero])
            map_add' := fun a b => hinjO (by rw [hx, map_add, map_add, hx, hx])
            commutes' := fun r => hinjO (by rw [hx, ψ.commutes, Algebra.algebraMap_self_apply]) }, fun φ => hx φ⟩

theorem natCard_cartierDual_algHom_eq
    (q : ℕ) [Fact q.Prime]
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O)
    (hOfix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O L x) = algebraMap O L x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn K, σ y = y) → ∃ x : O, algebraMap O L x = y)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀] [Coalgebra.IsCocomm O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[O] L), (∀ h : H₀, g h = σ (f h)) → g = f ^ c) :
    Nat.card (CartierDual O H₀ →ₐ[O] O) = q ^ a := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  have hcardD : Nat.card (CartierDual O H₀ →ₐ[O] L) = q ^ a := by
    rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero, CartierDual.finrank_eq, hrank]
  rw [← hcardD]
  apply Nat.card_eq_of_bijective (fun ψO : CartierDual O H₀ →ₐ[O] O => (Algebra.ofId O L).comp ψO)
  constructor
  · intro ψ₁ ψ₂ h
    refine AlgHom.ext fun φ => FaithfulSMul.algebraMap_injective O L ?_
    have := DFunLike.congr_fun h φ
    exact this
  · intro ψ
    obtain ⟨ψO, hψO⟩ := cartierDual_point_factors q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ ψ
    exact ⟨ψO, AlgHom.ext fun φ => hψO φ⟩

end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed.HopfPoints"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk exists_comp_antipode_convMul_eq_one natCard_algHom_eq_finrank_of_charZero point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal exists_quotientFlag_of_galoisStableChain_of_fixedPoints"
p2m_open "HopfAlgebra"

open HopfPoints

theorem cartierDual_point_pow_eq_one
    (q : ℕ) [Fact q.Prime]
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOdvr : IsDiscreteValuationRing O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀] [Coalgebra.IsCocomm O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (x : WithConv (CartierDual O H₀ →ₐ[O] O)) : x ^ q = 1 := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  obtain ⟨e, _he1, he2, he3, _he4⟩ := CartierDual.exists_algHomEquiv_groupLike (O) H₀
  let Φ : WithConv (CartierDual O H₀ →ₐ[O] O) → WithConv (CartierDual O H₀ →ₐ[O] L) :=
    fun y => WithConv.toConv ((Algebra.ofId O L).comp (WithConv.ofConv y))
  have hΦmul : ∀ y z, Φ (y * z) = Φ y * Φ z := by
    intro y z
    show WithConv.toConv ((Algebra.ofId O L).comp (WithConv.ofConv (y * z))) = _
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
    have h1 := congrArg (fun g : WithConv (CartierDual O H₀ →ₐ[O] L) => g h) hyz
    exact FaithfulSMul.algebraMap_injective O L h1
  let E' : WithConv (CartierDual O H₀ →ₐ[O] L)
      → GroupLike L (TensorProduct O L H₀) :=
    fun y => e L (WithConv.ofConv y)
  have hE'mul_val : ∀ y z, (E' (y * z)).val = (E' y).val * (E' z).val := fun y z =>
    he3 L (WithConv.ofConv y) (WithConv.ofConv z) (WithConv.ofConv (y * z)) (AlgHom.toLinearMap_convMul y z)
  have hE'one_val : (E' 1).val = 1 := by
    refine he2 L (WithConv.ofConv (1 : WithConv (CartierDual O H₀ →ₐ[O] L))) fun φ => ?_
    show (1 : WithConv (CartierDual O H₀ →ₐ[O] L)) φ = algebraMap O L (φ 1)
    rw [AlgHom.convOne_apply]
    exact congrArg (algebraMap O L) (CartierDual.counit_apply φ)
  have hE'pow_val : ∀ y (k : ℕ), (E' (y ^ k)).val = (E' y).val ^ k := by
    intro y k
    induction k with
    | zero => rw [pow_zero, pow_zero, hE'one_val]
    | succ k ih => rw [pow_succ, pow_succ, hE'mul_val, ih]
  have hE'inj : Function.Injective E' := fun y z h =>
    WithConv.ofConv_injective ((e L).injective h)
  have h1 : (E' (Φ x)).val ^ q = 1 :=
    groupLike_pow_eq_one q O hOdvr H₀ a hrank hpts hptq _ (E' (Φ x)).isGroupLikeElem_val
  have h2 : (E' ((Φ x) ^ q)).val = (E' 1).val := by rw [hE'pow_val, h1, hE'one_val]
  have h3 : (Φ x) ^ q = 1 := hE'inj (GroupLike.val_injective h2)
  apply hΦinj
  rw [hΦpow, h3, hΦone]

theorem cartierDual_points_residue_comp_ne
    (q : ℕ) [Fact q.Prime]
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOdvr : IsDiscreteValuationRing O)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀] [Coalgebra.IsCocomm O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (hq2 : q ≠ 2) (hOirr : Irreducible ((q : ℕ) : O))
    (x x' : WithConv (CartierDual O H₀ →ₐ[O] O)) (hne : x ≠ x') :
    (IsLocalRing.residue O).comp (WithConv.ofConv x).toRingHom
      ≠ (IsLocalRing.residue O).comp (WithConv.ofConv x').toRingHom := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  intro hres
  apply hne
  let κ := IsLocalRing.ResidueField O
  let r : O →ₐ[O] κ := Algebra.ofId O κ
  let R : WithConv (CartierDual O H₀ →ₐ[O] O) → WithConv (CartierDual O H₀ →ₐ[O] κ) :=
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
  let w : WithConv (CartierDual O H₀ →ₐ[O] O) := x * x' ^ k
  have hx'q : x' ^ q = 1 := cartierDual_point_pow_eq_one q O hOdvr H₀ a hrank hpts hptq x'
  have hRw : R w = R 1 := by
    show R (x * x' ^ k) = R 1
    rw [hRmul, hRx, ← hRpow, ← hk, hx'q]
  have hw1 : ∀ φ : CartierDual O H₀,
      w φ - algebraMap O O (Coalgebra.counit φ) ∈ IsLocalRing.maximalIdeal O := by
    intro φ
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    have h1 := congrArg (fun g : WithConv (CartierDual O H₀ →ₐ[O] κ) => g φ) hRw
    have h2 : (R 1) φ = IsLocalRing.residue O (algebraMap O O (Coalgebra.counit φ)) := by
      show algebraMap O κ ((1 : WithConv (CartierDual O H₀ →ₐ[O] O)) φ) = _
      rw [AlgHom.convOne_apply]
      rfl
    exact h1.trans h2
  have hwq : w ^ q = 1 := cartierDual_point_pow_eq_one q O hOdvr H₀ a hrank hpts hptq w
  have hw : w = 1 :=
    HopfAlgebra.point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal (O) q hq2 hOirr (CartierDual O H₀)
      w hw1 q (Nat.pos_of_ne_zero hq0) hwq
  calc x = x * x' ^ q := by rw [hx'q, mul_one]
    _ = (x * x' ^ k) * x' := by rw [hk, pow_succ, mul_assoc]
    _ = x' := by
        show w * x' = x'
        rw [hw, one_mul]

theorem cartierDual_eval_bijective
    (q : ℕ) [Fact q.Prime]
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O)
    (hOfix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O L x) = algebraMap O L x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn K, σ y = y) → ∃ x : O, algebraMap O L x = y)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀] [Coalgebra.IsCocomm O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[O] L), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (hq2 : q ≠ 2) (hOirr : Irreducible ((q : ℕ) : O)) :
    Function.Bijective (fun (a : CartierDual O H₀) (x : WithConv (CartierDual O H₀ →ₐ[O] O)) =>
      (WithConv.ofConv x) a) := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  let ι := WithConv (CartierDual O H₀ →ₐ[O] O)
  have hιcard : Nat.card ι = q ^ a := by
    rw [← natCard_cartierDual_algHom_eq q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ]
    exact Nat.card_congr ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite ι := Nat.finite_of_card_ne_zero (hιcard ▸ pow_ne_zero a hq0)
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank O (CartierDual O H₀) := by
    rw [Fintype.card_eq_nat_card, hιcard, CartierDual.finrank_eq, hrank]
  exact eval_bijective_of_card_eq_finrank_of_residue_comp_ne (O := O) (B := CartierDual O H₀)
    (fun x : ι => WithConv.ofConv x) hcard
    (fun i j hij => cartierDual_points_residue_comp_ne q O hOdvr H₀ a hrank hpts hptq hq2 hOirr i j hij)

theorem nonempty_linearEquiv_pi_zmod_of_natCard (q : ℕ) [Fact q.Prime] (V : Type) [AddCommGroup V] [Module (ZMod q) V] [Finite V]
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

theorem exists_bialgEquiv_monoidAlgebra_of_chiType
    (q : ℕ) [Fact q.Prime]
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O)
    (hOfix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O L x) = algebraMap O L x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn K, σ y = y) → ∃ x : O, algebraMap O L x = y)
    (H₀ : Type) [CommRing H₀] [HopfAlgebra O H₀]
    [Module.Finite O H₀] [Module.Flat O H₀] [Coalgebra.IsCocomm O H₀]
    (a : ℕ) (hrank : Module.finrank O H₀ = q ^ a)
    (hpts : Nat.card (WithConv (H₀ →ₐ[O] L)) = q ^ a)
    (hptq : ∀ f : WithConv (H₀ →ₐ[O] L), f ^ q = 1)
    (hχ : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (H₀ →ₐ[O] L), (∀ h : H₀, g h = σ (f h)) → g = f ^ c)
    (hq2 : q ≠ 2) (hOirr : Irreducible ((q : ℕ) : O)) :
    Nonempty (H₀ ≃ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O H₀ := Module.free_of_flat_of_isLocalRing
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  let Γ := WithConv (CartierDual O H₀ →ₐ[O] O)
  have hΓcard : Nat.card Γ = q ^ a := by
    rw [← natCard_cartierDual_algHom_eq q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ]
    exact Nat.card_congr ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩
  haveI : Finite Γ := Nat.finite_of_card_ne_zero (hΓcard ▸ pow_ne_zero a hq0)
  obtain ⟨ψ, -⟩ := CartierDual.exists_bialgEquiv_monoidAlgebra_of_points (O) (CartierDual O H₀) Γ (MonoidHom.id Γ)
    (cartierDual_eval_bijective q A O hOA hOdvr hOfix hOmax H₀ a hrank hpts hptq hχ hq2 hOirr)
  obtain ⟨e₁, -⟩ := CartierDual.exists_bialgEquiv_bidual (O) H₀
  obtain ⟨e₂, -⟩ := CartierDual.exists_bialgEquiv_bidual (O) (MonoidAlgebra O Γ)
  let e₃ : CartierDual O (CartierDual O H₀) ≃ₐc[O] CartierDual O (CartierDual O (MonoidAlgebra O Γ)) :=
    (CartierDual.congr ψ).symm
  let eΓ : H₀ ≃ₐc[O] MonoidAlgebra O Γ := e₁.trans (e₃.trans e₂.symm)
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
  let eZ : MonoidAlgebra O Γ ≃ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) :=
    BialgEquiv.ofBialgHom (MonoidAlgebra.mapDomainBialgHom O fh) (MonoidAlgebra.mapDomainBialgHom O gh)
      (by rw [← MonoidAlgebra.mapDomainBialgHom_comp, hfg, MonoidAlgebra.mapDomainBialgHom_id])
      (by rw [← MonoidAlgebra.mapDomainBialgHom_comp, hgf, MonoidAlgebra.mapDomainBialgHom_id])
  exact ⟨eΓ.trans eZ⟩

end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed.HopfPoints"

open _root_.HopfAlgebra _root_.P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed.HopfAlgebra HopfPoints in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (hOfix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O L x) = algebraMap O L x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn K, σ y = y) → ∃ x : O, algebraMap O L x = y)
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
    (D : Submonoid (WithConv (HO →ₐ[O] L)))
    (a : ℕ) (hcardD : Nat.card ↥D = q ^ a)
    (hD : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f ∈ D, ∀ g : WithConv (HO →ₐ[O] L), (∀ h : HO, g h = σ (f h)) → g = f ^ c) :
    ∃ p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p₀ ∧
      ∀ f : HO →ₐ[O] L,
        (∃ g : MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] L,
            g.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) = f) ↔
          WithConv.toConv f ∈ D := by
  classical
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Module.Free O HO := Module.free_of_flat_of_isLocalRing
  have hqp : q.Prime := Fact.out
  have hq0 : q ≠ 0 := hqp.ne_zero

  have hunit : ∀ f : WithConv (HO →ₐ[O] L), IsUnit f := by
    intro f
    obtain ⟨ν', -, h1, h2⟩ := HopfAlgebra.exists_comp_antipode_convMul_eq_one (WithConv.ofConv f)
    rw [WithConv.toConv_ofConv] at h1 h2
    exact IsUnit.of_mul_eq_one _ h2
  letI instG : CommGroup (WithConv (HO →ₐ[O] L)) := { groupOfIsUnit hunit with mul_comm := mul_comm }

  have hptqD : ∀ f ∈ D, f ^ q = 1 := by
    intro f hf
    have h := hD 1 (Subgroup.one_mem _) (q + 1)
      (fun ζ hζ => by rw [AlgEquiv.one_apply, pow_succ, hζ, one_mul]) f hf f (fun h => rfl)
    rw [pow_succ] at h
    exact mul_right_cancel (h.symm.trans (one_mul f).symm)

  let f₀ : HO →ₐ[O] L := WithConv.ofConv (1 : WithConv (HO →ₐ[O] L))
  haveI : Nontrivial HO := ⟨⟨1, 0, fun h => one_ne_zero (by rw [← map_one f₀, h, map_zero])⟩⟩
  have hcard : Nat.card (HO →ₐ[O] L) = Module.finrank O HO :=
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O HO L
  haveI : Finite (HO →ₐ[O] L) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact ((Module.finrank_pos_iff_of_free (R := O) HO).mpr inferInstance).ne')

  let M : Type := Additive (WithConv (HO →ₐ[O] L))
  haveI : Finite M := Finite.of_equiv _ (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ :
    WithConv (HO →ₐ[O] L) ≃ (HO →ₐ[O] L)).symm |>.of_equiv _  Additive.ofMul
  let pts : WithConv (HO →ₐ[O] L) ≃ M := Additive.ofMul
  have hadd : ∀ f g, pts (f * g) = pts f + pts g := fun _ _ => rfl
  have hpts1 : pts 1 = 0 := rfl

  have hτ : ∀ σ ∈ A.inertiaSubgroupIn K, ∃ τ : L →ₐ[O] L, ∀ z, τ z = σ z :=
    fun σ hσ => ⟨{ (σ : L →+* L) with
      commutes' := fun o => (hOfix σ).mp hσ o }, fun _ => rfl⟩
  let act : (L ≃ₐ[K] L) → M → M := fun σ x =>
    if hσ : σ ∈ A.inertiaSubgroupIn K then
      pts (WithConv.toConv ((hτ σ hσ).choose.comp (WithConv.ofConv (pts.symm x))))
    else x
  have act_def : ∀ σ x, act σ x =
      if hσ : σ ∈ A.inertiaSubgroupIn K then
        pts (WithConv.toConv ((hτ σ hσ).choose.comp (WithConv.ofConv (pts.symm x))))
      else x := fun _ _ => rfl
  have hact_of_not_mem : ∀ σ, σ ∉ A.inertiaSubgroupIn K → ∀ x, act σ x = x := fun σ hσ x => by
    rw [act_def, dif_neg hσ]
  have hrow_act : ∀ (σ : L ≃ₐ[K] L)
      (f g : WithConv (HO →ₐ[O] L)),
      (∀ h : HO, g h = σ (f h)) → pts g = act σ (pts f) := by
    intro σ f g hfg
    have hσ : σ ∈ A.inertiaSubgroupIn K := by
      rw [hOfix]
      intro o
      have h1 : σ ((WithConv.ofConv f) (algebraMap O HO o)) = (WithConv.ofConv g) (algebraMap O HO o) :=
        (hfg _).symm
      rw [(WithConv.ofConv f).commutes o, (WithConv.ofConv g).commutes o] at h1
      exact h1
    rw [act_def, dif_pos hσ, Equiv.symm_apply_apply]
    congr 1
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    exact (hfg h).trans ((hτ σ hσ).choose_spec (f h)).symm

  have hDinv : ∀ f ∈ D, f⁻¹ ∈ D := by
    intro f hf
    have hunit : f * f ^ (q - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hqp.one_lt.le, hptqD f hf]
    rw [show f⁻¹ = f ^ (q - 1) from inv_eq_of_mul_eq_one_right hunit]
    exact pow_mem hf _
  let S : AddSubgroup M :=
    { carrier := {m | Additive.toMul m ∈ D}
      zero_mem' := D.one_mem
      add_mem' := fun {x y} hx hy => D.mul_mem hx hy
      neg_mem' := fun {x} hx => hDinv _ hx }
  have hmemS : ∀ m : M, m ∈ S ↔ Additive.toMul m ∈ D := fun _ => Iff.rfl
  have hcardS : Nat.card ↥S = q ^ a := by
    rw [← hcardD]
    exact Nat.card_congr ⟨fun m => ⟨Additive.toMul m.1, m.2⟩, fun d => ⟨Additive.ofMul d.1, d.2⟩, fun _ => rfl, fun _ => rfl⟩
  let N : Fin (1 + 1) → AddSubgroup M := fun i => if (i : ℕ) = 0 then S else ⊤
  have hN : ∀ i, N i = if (i : ℕ) = 0 then S else ⊤ := fun _ => rfl
  have h0 : ((0 : Fin (1 + 1)) : ℕ) = 0 := rfl
  have hmono : ∀ i : Fin 1, N i.castSucc ≤ N i.succ := by
    intro i
    have h1 : ((i.succ : Fin (1 + 1)) : ℕ) ≠ 0 := by rw [Fin.val_succ]; exact Nat.succ_ne_zero _
    rw [hN i.succ, if_neg h1]
    exact le_top
  have htop : N (Fin.last 1) = ⊤ := by
    rw [hN, if_neg (show ((Fin.last 1 : Fin (1 + 1)) : ℕ) ≠ 0 by decide)]
  have hstab : ∀ (i : Fin (1 + 1)) (σ : L ≃ₐ[K] L) (x : M),
      x ∈ N i → act σ x ∈ N i := by
    intro i σ x hx
    rw [hN] at hx ⊢
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi] at hx ⊢
      by_cases hσ : σ ∈ A.inertiaSubgroupIn K
      · obtain ⟨c, hc⟩ := S17.SurjMonAlgGen.exists_apply_eq_pow_of_pow_eq_one q hq0 σ
        have hfg : ∀ h : HO, (WithConv.toConv ((hτ σ hσ).choose.comp (WithConv.ofConv (pts.symm x)))) h = σ ((pts.symm x) h) :=
          fun h => (hτ σ hσ).choose_spec _
        have key := hD σ hσ c hc (pts.symm x) hx _ hfg
        rw [act_def, dif_pos hσ, key]
        exact D.pow_mem hx c
      · rw [hact_of_not_mem σ hσ x]
        exact hx
    · rw [if_neg hi] at hx ⊢
      exact AddSubgroup.mem_top _
  obtain ⟨B, instCR, instHA, π, -, -, hflat, hπsurj, -, -, -, hfactor, hcocomm, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints O (FaithfulSMul.algebraMap_injective O L)
      (S17.SurjMonAlgGen.fixedPoints_of_inertia A O hOfix hOmax)
      HO M pts hadd act hrow_act 1 N hmono htop hstab
  haveI : Module.Flat O (B 0) := hflat 0
  haveI : Module.Finite O (B 0) := (hfin inferInstance 0).1
  haveI : Coalgebra.IsCocomm O (B 0) := hcocomm inferInstance 0
  let π₀ : HO →ₐc[O] B 0 := π 0
  have hrank : Module.finrank O (B 0) = q ^ a := by
    rw [(hfin inferInstance 0).2 (by decide), hN, if_pos h0, ← hcardS]
  have hfac0 : ∀ f : HO →ₐ[O] L,
      (∃ g : B 0 →ₐ[O] L, g.comp (π₀ : HO →ₐ[O] B 0) = f) ↔ WithConv.toConv f ∈ D := by
    intro f
    rw [hfactor 0 f, hN, if_pos h0, hmemS]
    rfl
  have hcomp_inj : ∀ g₁ g₂ : B 0 →ₐ[O] L,
      g₁.comp (π₀ : HO →ₐ[O] B 0) = g₂.comp (π₀ : HO →ₐ[O] B 0) → g₁ = g₂ := by
    intro g₁ g₂ h
    refine AlgHom.ext fun b => ?_
    obtain ⟨x, rfl⟩ := hπsurj 0 b
    exact DFunLike.congr_fun h x
  have hpts_comp : ∀ (g : WithConv (B 0 →ₐ[O] L)) (k : ℕ),
      (WithConv.ofConv (g ^ k)).comp (π₀ : HO →ₐ[O] B 0)
        = WithConv.ofConv ((WithConv.toConv ((WithConv.ofConv g).comp (π₀ : HO →ₐ[O] B 0))) ^ k) := by
    intro g k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero]
        refine AlgHom.ext fun x => ?_
        change algebraMap O L (Coalgebra.counit (π₀ x))
          = algebraMap O L (Coalgebra.counit x)
        rw [CoalgHomClass.counit_comp_apply]
    | succ k ih =>
        rw [pow_succ, pow_succ, AlgHom.convMul_comp_bialgHom_distrib, ih, WithConv.toConv_ofConv]
  have hpts0 : Nat.card (WithConv (B 0 →ₐ[O] L)) = q ^ a := by
    rw [Nat.card_congr (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ :
      WithConv (B 0 →ₐ[O] L) ≃ (B 0 →ₐ[O] L))]
    rw [← hcardD]
    apply Nat.card_eq_of_bijective
      (fun g : B 0 →ₐ[O] L =>
        (⟨WithConv.toConv (g.comp (π₀ : HO →ₐ[O] B 0)), (hfac0 _).mp ⟨g, rfl⟩⟩ : ↥D))
    constructor
    · intro g₁ g₂ h
      have h1 := congrArg Subtype.val h
      exact hcomp_inj _ _ (WithConv.toConv_injective h1)
    · rintro ⟨x, hx⟩
      obtain ⟨g, hg⟩ := (hfac0 (WithConv.ofConv x)).mpr (by rwa [WithConv.toConv_ofConv])
      refine ⟨g, Subtype.ext ?_⟩
      simp only [hg, WithConv.toConv_ofConv]
  have hptq0 : ∀ g : WithConv (B 0 →ₐ[O] L), g ^ q = 1 := by
    intro g
    have hg : (WithConv.toConv ((WithConv.ofConv g).comp (π₀ : HO →ₐ[O] B 0))) ^ q = 1 :=
      hptqD _ ((hfac0 _).mp ⟨WithConv.ofConv g, rfl⟩)
    apply WithConv.ofConv_injective
    apply hcomp_inj
    rw [hpts_comp, hg]
    have hz := hpts_comp g 0
    rw [pow_zero, pow_zero] at hz
    exact hz.symm
  have hχ0 : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f g : WithConv (B 0 →ₐ[O] L), (∀ b : B 0, g b = σ (f b)) → g = f ^ c := by
    intro σ hσ c hc f g hfg
    let f' : WithConv (HO →ₐ[O] L) :=
      WithConv.toConv ((WithConv.ofConv f).comp (π₀ : HO →ₐ[O] B 0))
    let g' : WithConv (HO →ₐ[O] L) :=
      WithConv.toConv ((WithConv.ofConv g).comp (π₀ : HO →ₐ[O] B 0))
    have hf'g' : ∀ x : HO, g' x = σ (f' x) := fun x => hfg (π₀ x)
    have hmemf : f' ∈ D := (hfac0 _).mp ⟨WithConv.ofConv f, rfl⟩
    have h3 : g' = f' ^ c := hD σ hσ c hc f' hmemf g' hf'g'
    apply WithConv.ofConv_injective
    apply hcomp_inj
    rw [hpts_comp]
    change WithConv.ofConv g' = WithConv.ofConv (f' ^ c)
    rw [h3]
  obtain ⟨eB⟩ := exists_bialgEquiv_monoidAlgebra_of_chiType q A O hOA hOdvr hOfix hOmax (B 0) a hrank hpts0 hptq0 hχ0 hq2 hOirr
  let p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) := eB.toBialgHom.comp π₀
  refine ⟨p₀, (EquivLike.surjective eB).comp (hπsurj 0), fun f => ?_⟩
  rw [← hfac0 f]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.comp (eB.toBialgHom : B 0 →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))), ?_⟩
    rw [← hg]
    exact AlgHom.ext fun x => rfl
  · rintro ⟨g, hg⟩
    refine ⟨g.comp (eB.symm.toBialgHom : MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] B 0), ?_⟩
    rw [← hg]
    refine AlgHom.ext fun x => ?_
    change g (eB.symm (eB (π₀ x))) = g (π₀ x)
    congr 1
    exact eB.toEquiv.symm_apply_apply (π₀ x)

end
end S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed (solution)
