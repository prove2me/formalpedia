-- Prove2me | solution 1 for MvFormalGroup.cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4b363045-d563-585b-98db-ebf17c566300

import Mathlib
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Theorems.Thm_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace MvFormalGroup
p2m_export "MvFormalGroup" "counit_apply_eq_zero_of_comul_eq_adicEval hasSubst_toPowerSeries map toPowerSeries adicEval adicEval_coe adicEval_X adicEvalAlgHom coe_adicEvalAlgHom adicEval_subst map_adicEval algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
namespace HBI
p2m_open "MvFormalGroup"

open scoped TensorProduct
open MvPowerSeries

section Fibre

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  (R : Type*) [CommRing R] [HopfAlgebra 𝓞 R]

private noncomputable def θ : R ⊗[𝓞] R →ₐ[𝓞] (ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (S := 𝓞)).comp
      (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] ZMod p ⊗[𝓞] R))
    (((Algebra.TensorProduct.includeRight :
        ZMod p ⊗[𝓞] R →ₐ[ZMod p] (ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R)).restrictScalars 𝓞).comp
      (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] ZMod p ⊗[𝓞] R))
    (fun x y => by
      show _ * _ = _ * _
      exact mul_comm (G := (ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R)) _ _)

private theorem θ_tmul (r r' : R) :
    θ p R (r ⊗ₜ[𝓞] r') = ((1 : ZMod p) ⊗ₜ[𝓞] r) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[𝓞] r') := by
  rw [θ, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem comul_one_tmul (r : R) :
    Coalgebra.comul (R := ZMod p) ((1 : ZMod p) ⊗ₜ[𝓞] r) = θ p R (Coalgebra.comul (R := 𝓞) r) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction (Coalgebra.comul (R := 𝓞) r) using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul a b => rw [θ_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add s t hs ht => rw [TensorProduct.tmul_add, LinearEquiv.map_add, hs, ht, map_add]

private theorem counit_one_tmul (r : R) :
    Coalgebra.counit (R := ZMod p) ((1 : ZMod p) ⊗ₜ[𝓞] r) =
      algebraMap 𝓞 (ZMod p) (Coalgebra.counit (R := 𝓞) r) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, mul_one]

private theorem natCast_eq_zero (S : Type*) [Ring S] [Algebra (ZMod p) S] : (p : S) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) S) p, ZMod.natCast_self, map_zero]

end Fibre

section Trunc

variable {𝓞 : Type*} [CommRing 𝓞] {σ : Type*}

private theorem mem_span_X_pow [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ 𝓞, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ 𝓞) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries σ 𝓞 := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ 𝓞) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ 𝓞) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ 𝓞) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ 𝓞) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ 𝓞) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

variable [Fintype σ] [DecidableEq σ]

private noncomputable def boxTrunc (N : ℕ) (K : MvPowerSeries σ 𝓞) : MvPolynomial σ 𝓞 :=
  ∑ m ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => N - 1),
    MvPolynomial.monomial m (coeff m K)

private theorem coeff_boxTrunc (N : ℕ) (K : MvPowerSeries σ 𝓞) (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (boxTrunc N K) =
      if e ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => N - 1) then coeff e K else 0 := by
  rw [boxTrunc, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']

private theorem mem_Iic_iff {N : ℕ} (hN : 1 ≤ N) (e : σ →₀ ℕ) :
    e ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => N - 1) ↔ ∀ s, e s < N := by
  rw [Finset.mem_Iic, Finsupp.le_def]
  refine forall_congr' fun s => ?_
  rw [Finsupp.coe_equivFunOnFinite_symm]
  omega

private theorem adicEval_bot_eq_aeval_boxTrunc {S : Type*} [CommRing S] [Algebra 𝓞 S]
    {y : σ → S} (hy : ∀ s, IsNilpotent (y s)) {N : ℕ} (hN : 1 ≤ N) (hyN : ∀ s, y s ^ N = 0)
    (K : MvPowerSeries σ 𝓞) :
    MvFormalGroup.adicEval (⊥ : Ideal S) y K = MvPolynomial.aeval y (boxTrunc N K) := by
  have hy' : ∀ s, y s ∈ (⊥ : Ideal S).radical := fun s =>
    show y s ∈ nilradical S from mem_nilradical.mpr (hy s)

  have hrem : K - (boxTrunc N K : MvPolynomial σ 𝓞) ∈
      Ideal.span ((fun s => (X s : MvPowerSeries σ 𝓞) ^ N) '' ((Finset.univ : Finset σ) : Set σ)) := by
    refine mem_span_X_pow N Finset.univ _ fun e he => ?_
    rw [map_sub, MvPolynomial.coeff_coe, coeff_boxTrunc, if_pos ((mem_Iic_iff hN e).mpr fun s => he s
      (Finset.mem_univ s)), sub_self]
  have hkill : MvFormalGroup.adicEvalAlgHom (R := 𝓞) (⊥ : Ideal S) hy'
      (K - (boxTrunc N K : MvPolynomial σ 𝓞)) = 0 := by
    have hle : Ideal.map (MvFormalGroup.adicEvalAlgHom (R := 𝓞) (⊥ : Ideal S) hy')
        (Ideal.span ((fun s => (X s : MvPowerSeries σ 𝓞) ^ N) '' ((Finset.univ : Finset σ) : Set σ))) = ⊥ := by
      rw [Ideal.map_span, Ideal.span_eq_bot]
      rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
      change MvFormalGroup.adicEvalAlgHom (R := 𝓞) (⊥ : Ideal S) hy' ((X s : MvPowerSeries σ 𝓞) ^ N) = 0
      rw [map_pow, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X, hyN]
    have h := Ideal.mem_map_of_mem (MvFormalGroup.adicEvalAlgHom (R := 𝓞) (⊥ : Ideal S) hy') hrem
    rwa [hle, Ideal.mem_bot] at h
  rw [map_sub, sub_eq_zero, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_coe] at hkill
  exact hkill

end Trunc

end MvFormalGroup.HBI

namespace MvFormalGroup
p2m_export "MvFormalGroup" "counit_apply_eq_zero_of_comul_eq_adicEval hasSubst_toPowerSeries map toPowerSeries adicEval adicEval_coe adicEval_X adicEvalAlgHom coe_adicEvalAlgHom adicEval_subst map_adicEval algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical"
namespace HBI
p2m_open "MvFormalGroup"

open scoped TensorProduct
open MvPowerSeries

section Fibre2

private theorem map_mem_radical_span_natCast {𝓞 A C : Type*} [CommRing 𝓞] [CommRing A] [CommRing C]
    [Algebra 𝓞 A] [Algebra 𝓞 C] (p : ℕ) (φ : A →ₐ[𝓞] C) {s : A}
    (hs : s ∈ (Ideal.span {(p : A)}).radical) : φ s ∈ (Ideal.span {(p : C)}).radical := by
  obtain ⟨n, hn⟩ := hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨n, ?_⟩
  rw [← map_pow, ← ht, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  {R : Type*} [CommRing R] [HopfAlgebra 𝓞 R] {d : ℕ}

private theorem prod_tmul_one {k A C : Type*} [CommRing k] [CommRing A] [CommRing C] [Algebra k A] [Algebra k C]
    {ι : Type*} (s : Finset ι) (u : ι → A) :
    (∏ j ∈ s, u j ⊗ₜ[k] (1 : C)) = (∏ j ∈ s, u j) ⊗ₜ[k] (1 : C) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

private theorem prod_one_tmul {k A C : Type*} [CommRing k] [CommRing A] [CommRing C] [Algebra k A] [Algebra k C]
    {ι : Type*} (s : Finset ι) (u : ι → C) :
    (∏ j ∈ s, (1 : A) ⊗ₜ[k] u j) = (1 : A) ⊗ₜ[k] (∏ j ∈ s, u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

private theorem aeval_monomial_eq_smul_prod (x : Fin d → ZMod p ⊗[𝓞] R) (a : Fin d →₀ ℕ) (c : 𝓞) :
    MvPolynomial.aeval x (MvPolynomial.monomial a c) =
      algebraMap 𝓞 (ZMod p) c • ∏ j, x j ^ a j := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun j => pow_zero _),
    IsScalarTower.algebraMap_apply 𝓞 (ZMod p) (ZMod p ⊗[𝓞] R), Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]

private theorem aeval_elim_monomial_eq_smul_tmul (x : Fin d → ZMod p ⊗[𝓞] R) (m : (Fin d ⊕ Fin d) →₀ ℕ)
    (c : 𝓞) :
    MvPolynomial.aeval (Sum.elim (fun j => x j ⊗ₜ[ZMod p] (1 : ZMod p ⊗[𝓞] R))
        (fun j => (1 : ZMod p ⊗[𝓞] R) ⊗ₜ[ZMod p] x j)) (MvPolynomial.monomial m c) =
      algebraMap 𝓞 (ZMod p) c •
        ((∏ j, x j ^ m (Sum.inl j)) ⊗ₜ[ZMod p] (∏ j, x j ^ m (Sum.inr j))) := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun j => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Algebra.TensorProduct.tmul_pow, one_pow]
  rw [prod_tmul_one, prod_one_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    IsScalarTower.algebraMap_apply 𝓞 (ZMod p) ((ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R)),
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

private theorem D_one (D : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hDii : ∀ a b : ZMod p ⊗[𝓞] R, D (a * b) =
      D a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D b) : D 1 = 0 := by
  have h := hDii 1 1
  rw [mul_one, Bialgebra.counit_one, mul_one, one_mul] at h
  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

private theorem D_mul_eq_zero (D : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hDii : ∀ a b : ZMod p ⊗[𝓞] R, D (a * b) =
      D a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D b)
    {a b : ZMod p ⊗[𝓞] R} (ha : Coalgebra.counit (R := ZMod p) a = 0)
    (hb : Coalgebra.counit (R := ZMod p) b = 0) : D (a * b) = 0 := by
  rw [hDii, ha, hb, mul_zero, zero_mul, add_zero]

private theorem counit_prod_pow_eq_zero (x : Fin d → ZMod p ⊗[𝓞] R)
    (hεx : ∀ j, Coalgebra.counit (R := ZMod p) (x j) = 0) {b : Fin d → ℕ} (hb : b ≠ 0) :
    Coalgebra.counit (R := ZMod p) (∏ j, x j ^ b j) = 0 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, b j₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (funext h)
  rw [← Bialgebra.counitAlgHom_apply, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
  rw [map_pow, Bialgebra.counitAlgHom_apply, hεx, zero_pow hj₀]

private theorem prod_pow_single (x : Fin d → ZMod p ⊗[𝓞] R) (j₀ : Fin d) :
    (∏ j, x j ^ (Pi.single j₀ 1 : Fin d → ℕ) j) = x j₀ := by
  rw [Finset.prod_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, pow_zero])
    (fun h => absurd (Finset.mem_univ j₀) h), Pi.single_eq_same, pow_one]

private theorem D_prod_pow (x : Fin d → ZMod p ⊗[𝓞] R)
    (hεx : ∀ j, Coalgebra.counit (R := ZMod p) (x j) = 0)
    (i : Fin d) (D : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hDi : ∀ j, D (x j) = if i = j then 1 else 0)
    (hDii : ∀ a b : ZMod p ⊗[𝓞] R, D (a * b) =
      D a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D b)
    (b : Fin d → ℕ) :
    D (∏ j, x j ^ b j) = if b = Pi.single i 1 then 1 else 0 := by
  classical
  by_cases hb0 : b = 0
  · subst hb0
    have h1 : (∏ j, x j ^ (0 : Fin d → ℕ) j) = 1 := by simp
    rw [h1, D_one p D hDii, if_neg]
    intro h
    have := congrFun h i
    simp at this
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, b j₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hb0 (funext h)
  by_cases hb1 : b = Pi.single j₀ 1
  · subst hb1
    rw [prod_pow_single, hDi]
    by_cases hij : i = j₀
    · subst hij; simp
    · rw [if_neg hij, if_neg]
      intro h
      apply hij
      have h' := congrFun h i
      rw [Pi.single_eq_same] at h'
      by_contra hne
      rw [Pi.single_eq_of_ne hne] at h'
      exact one_ne_zero h'.symm
  ·
    let b' : Fin d → ℕ := b - Pi.single j₀ 1
    have hbb' : b = b' + Pi.single j₀ 1 := by
      funext j
      simp only [b', Pi.add_apply, Pi.sub_apply]
      by_cases hj : j = j₀
      · subst hj; rw [Pi.single_eq_same]; omega
      · rw [Pi.single_eq_of_ne hj]; omega
    have hb'0 : b' ≠ 0 := by
      intro h
      apply hb1
      rw [hbb', h, zero_add]
    have hsplit : (∏ j, x j ^ b j) = (∏ j, x j ^ b' j) * x j₀ := by
      conv_lhs => rw [hbb']
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [prod_pow_single]
    rw [hsplit, D_mul_eq_zero p D hDii (counit_prod_pow_eq_zero p x hεx hb'0) (hεx j₀), if_neg]
    intro h
    apply hb1
    have : j₀ = i := by
      by_contra hne
      have h' := congrFun h j₀
      rw [Pi.single_eq_of_ne hne] at h'
      exact hj₀ h'
    rw [h, this]

end Fibre2

end MvFormalGroup.HBI

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞)
    (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (i : Fin d) (D : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hDi : ∀ j, D ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = if i = j then 1 else 0)
    (hDii : ∀ a b : ZMod p ⊗[𝓞] R, D (a * b) =
      D a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D b)
    (L : MvPowerSeries (Fin d) 𝓞 → MvPowerSeries (Fin d) 𝓞)
    (hL : ∀ (H : MvPowerSeries (Fin d) 𝓞) (a : Fin d →₀ ℕ),
      (L H).coeff a = (subst F.toPowerSeries H).coeff (a.sumElim (Finsupp.single i 1)))
    (n : ℕ) (H : MvPowerSeries (Fin d) 𝓞) :
    (D ^ n) ((1 : ZMod p) ⊗ₜ[𝓞] π H) = algebraMap 𝓞 (ZMod p) ((L^[n] H).constantCoeff) := by
  classical

  haveI : IsAdicComplete (Ideal.span {(p : R)}) R :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p R
  haveI : IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R ⊗[𝓞] R)

  let iR : R →ₐ[𝓞] ZMod p ⊗[𝓞] R := Algebra.TensorProduct.includeRight
  have hiR : ∀ r, iR r = (1 : ZMod p) ⊗ₜ[𝓞] r := fun r => rfl
  let xb : Fin d → ZMod p ⊗[𝓞] R := fun j => iR (π (X j))
  have hxb : ∀ j, xb j = (1 : ZMod p) ⊗ₜ[𝓞] π (X j) := fun j => rfl

  have hεX : ∀ j, Coalgebra.counit (R := 𝓞) (π (X j)) = 0 :=
    MvFormalGroup.counit_apply_eq_zero_of_comul_eq_adicEval p F R (fun j => π (X j)) hπX hπΔ
  have hεxb : ∀ j, Coalgebra.counit (R := ZMod p) (xb j) = 0 := fun j => by
    rw [hxb, MvFormalGroup.HBI.counit_one_tmul, hεX, map_zero]
  have hDi' : ∀ j, D (xb j) = if i = j then 1 else 0 := hDi

  have hnil : ∀ j, ∃ e : ℕ, xb j ^ e = 0 := by
    intro j
    obtain ⟨e, he⟩ := hπX j
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp he
    refine ⟨e, ?_⟩
    show iR (π (X j)) ^ e = 0
    rw [← map_pow, ← ht, map_mul, map_natCast, MvFormalGroup.HBI.natCast_eq_zero p (ZMod p ⊗[𝓞] R),
      mul_zero]
  choose e he using hnil
  obtain ⟨N, hN2, hxbN⟩ : ∃ N : ℕ, 2 ≤ N ∧ ∀ j, xb j ^ N = 0 := by
    refine ⟨2 + ∑ j, e j, by omega, fun j => pow_eq_zero_of_le ?_ (he j)⟩
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ j)
    omega
  have hN1 : 1 ≤ N := by omega
  have hxbnil : ∀ j, IsNilpotent (xb j) := fun j => ⟨N, hxbN j⟩
  have hxbrad : ∀ j, xb j ∈ (⊥ : Ideal _).radical := fun j =>
    show xb j ∈ nilradical _ from mem_nilradical.mpr (hxbnil j)

  let y₂ : Fin d ⊕ Fin d → (ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R) :=
    Sum.elim (fun j => xb j ⊗ₜ[ZMod p] (1 : ZMod p ⊗[𝓞] R)) (fun j => (1 : ZMod p ⊗[𝓞] R) ⊗ₜ[ZMod p] xb j)
  have hy₂N : ∀ s, y₂ s ^ N = 0 := by
    rintro (j | j)
    · show (xb j ⊗ₜ[ZMod p] (1 : ZMod p ⊗[𝓞] R)) ^ N = 0
      rw [Algebra.TensorProduct.tmul_pow, hxbN, TensorProduct.zero_tmul]
    · show ((1 : ZMod p ⊗[𝓞] R) ⊗ₜ[ZMod p] xb j) ^ N = 0
      rw [Algebra.TensorProduct.tmul_pow, hxbN, TensorProduct.tmul_zero]
  have hy₂nil : ∀ s, IsNilpotent (y₂ s) := fun s => ⟨N, hy₂N s⟩

  have E1 : ∀ G, iR (π G) = MvFormalGroup.adicEval (⊥ : Ideal _) xb G := fun G =>
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal _) (iR.comp π)
      hxbrad G

  have E5 : ∀ G, Coalgebra.counit (R := 𝓞) (π G) = MvPowerSeries.constantCoeff G := by
    intro G
    let ψ₁ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 := (Bialgebra.counitAlgHom 𝓞 R).comp π
    let ψ₂ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 :=
      { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) 𝓞 →+* 𝓞) with
        commutes' := fun r => by
          show MvPowerSeries.constantCoeff (algebraMap 𝓞 (MvPowerSeries (Fin d) 𝓞) r) = algebraMap 𝓞 𝓞 r
          rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C] }
    have h0 : ∀ s, ψ₁ (X s) = ψ₂ (X s) := fun s => by
      show Coalgebra.counit (π (X s)) = MvPowerSeries.constantCoeff (X s)
      rw [hεX, MvPowerSeries.constantCoeff_X]
    have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal 𝓞) ψ₁
      (fun s => by rw [h0 s]; show MvPowerSeries.constantCoeff (X s) ∈ _
                   rw [MvPowerSeries.constantCoeff_X]; exact zero_mem _) G
    have h2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal 𝓞) ψ₂
      (fun s => by show MvPowerSeries.constantCoeff (X s) ∈ _
                   rw [MvPowerSeries.constantCoeff_X]; exact zero_mem _) G
    have h3 : (fun s => ψ₁ (X s)) = fun s => ψ₂ (X s) := funext h0
    change ψ₁ G = ψ₂ G
    rw [h1, h2, h3]

  have hyrad : ∀ s, Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)) s ∈
      (Ideal.span {(p : R ⊗[𝓞] R)}).radical := by
    rintro (j | j)
    · have h := MvFormalGroup.HBI.map_mem_radical_span_natCast p
        (Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R) (hπX j)
      rwa [Algebra.TensorProduct.includeLeft_apply] at h
    · have h := MvFormalGroup.HBI.map_mem_radical_span_natCast p
        (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R) (hπX j)
      rwa [Algebra.TensorProduct.includeRight_apply] at h
  have E3 : ∀ j, Coalgebra.comul (R := ZMod p) (xb j) =
      MvFormalGroup.adicEval (⊥ : Ideal _) y₂ (F.toPowerSeries j) := by
    intro j
    rw [hxb, MvFormalGroup.HBI.comul_one_tmul, hπΔ]
    refine (MvFormalGroup.map_adicEval (S' := (ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R))
      (Ideal.span {(p : R ⊗[𝓞] R)}) ⊥ (MvFormalGroup.HBI.θ p R)
      ⟨{(p : R ⊗[𝓞] R)}, by rw [Finset.coe_singleton]⟩ (fun s hs => ?_) hyrad (F.toPowerSeries j)).trans ?_
    · obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      rw [map_mul, map_natCast,
        MvFormalGroup.HBI.natCast_eq_zero p ((ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R)), mul_zero]
      exact Ideal.zero_mem _
    · congr 1
      funext s
      rcases s with j' | j'
      · simp only [Sum.elim_inl]
        rw [MvFormalGroup.HBI.θ_tmul]
        rfl
      · simp only [Sum.elim_inr]
        rw [MvFormalGroup.HBI.θ_tmul]
        rfl

  have E4 : ∀ G, Coalgebra.comul (R := ZMod p) (iR (π G)) =
      MvFormalGroup.adicEval (⊥ : Ideal _) y₂ (subst F.toPowerSeries G) := by
    intro G
    let ψ₃ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] (ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R) :=
      ((Bialgebra.comulAlgHom (ZMod p) (ZMod p ⊗[𝓞] R)).restrictScalars 𝓞).comp (iR.comp π)
    have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
      (S := (ZMod p ⊗[𝓞] R) ⊗[ZMod p] (ZMod p ⊗[𝓞] R)) (⊥ : Ideal _) ψ₃
      (fun s => ⟨N, by
        show (Bialgebra.comulAlgHom (ZMod p) (ZMod p ⊗[𝓞] R) (xb s)) ^ N ∈ _
        rw [← map_pow, hxbN, map_zero]
        exact Submodule.zero_mem _⟩) G
    have h4 : (fun s => ψ₃ (X s)) = fun s => MvFormalGroup.adicEval (⊥ : Ideal _) y₂ (F.toPowerSeries s) :=
      funext fun s => E3 s
    rw [h4, ← MvFormalGroup.adicEval_subst (⊥ : Ideal _) (fun s => ⟨N, by
        rw [hy₂N]
        exact Submodule.zero_mem _⟩) F.hasSubst_toPowerSeries G] at h
    exact h

  induction n generalizing H with
  | zero =>
    rw [pow_zero, CartierDual.one_apply, Function.iterate_zero_apply, MvFormalGroup.HBI.counit_one_tmul, E5]
  | succ n ih =>
    rw [pow_succ, CartierDual.mul_apply, Function.iterate_succ_apply, ← ih (L H), ← hiR (π H), E4 H,
      MvFormalGroup.HBI.adicEval_bot_eq_aeval_boxTrunc hy₂nil hN1 hy₂N, MvFormalGroup.HBI.boxTrunc,
      map_sum, map_sum, ← hiR (π (L H)), E1 (L H),
      MvFormalGroup.HBI.adicEval_bot_eq_aeval_boxTrunc hxbnil hN1 hxbN, MvFormalGroup.HBI.boxTrunc,
      map_sum, map_sum]

    let K : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 := subst F.toPowerSeries H
    let T : ((Fin d ⊕ Fin d) →₀ ℕ) → ZMod p := fun m =>
      algebraMap 𝓞 (ZMod p) (coeff m K) •
        ((D ^ n) (∏ j, xb j ^ m (Sum.inl j)) *
          (if (fun j => m (Sum.inr j)) = Pi.single i 1 then (1 : ZMod p) else 0))
    let S : (Fin d →₀ ℕ) → ZMod p := fun a =>
      algebraMap 𝓞 (ZMod p) ((L H).coeff a) • (D ^ n) (∏ j, xb j ^ a j)
    have stepL : ∀ m ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin d ⊕ Fin d => N - 1),
        TensorProduct.dualDistrib (ZMod p) (ZMod p ⊗[𝓞] R) (ZMod p ⊗[𝓞] R)
          (CartierDual.toDual (ZMod p) (ZMod p ⊗[𝓞] R) (D ^ n) ⊗ₜ[ZMod p]
            CartierDual.toDual (ZMod p) (ZMod p ⊗[𝓞] R) D)
          (MvPolynomial.aeval y₂ (MvPolynomial.monomial m (coeff m K))) = T m := by
      intro m _
      simp only [y₂]
      rw [MvFormalGroup.HBI.aeval_elim_monomial_eq_smul_tmul p xb m, map_smul,
        TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply,
        MvFormalGroup.HBI.D_prod_pow p xb hεxb i D hDi' hDii]
    have stepR : ∀ a ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N - 1),
        (D ^ n) (MvPolynomial.aeval xb (MvPolynomial.monomial a ((L H).coeff a))) = S a := by
      intro a _
      rw [MvFormalGroup.HBI.aeval_monomial_eq_smul_prod p xb a, map_smul]
    rw [Finset.sum_congr rfl stepL, Finset.sum_congr rfl stepR]

    let Φ : (Fin d →₀ ℕ) ↪ ((Fin d ⊕ Fin d) →₀ ℕ) :=
      ⟨fun a => a.sumElim (Finsupp.single i 1), fun a a' h => by
        ext j
        have := DFunLike.congr_fun h (Sum.inl j)
        simpa only [Finsupp.sumElim_inl] using this⟩
    have hΦ : ∀ a, Φ a = a.sumElim (Finsupp.single i 1) := fun a => rfl
    have hmemi : ∀ a : Fin d →₀ ℕ, a ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N - 1) →
        Φ a ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin d ⊕ Fin d => N - 1) := by
      intro a ha
      rw [MvFormalGroup.HBI.mem_Iic_iff hN1] at ha ⊢
      rintro (j | j)
      · rw [hΦ, Finsupp.sumElim_inl]; exact ha j
      · rw [hΦ, Finsupp.sumElim_inr, Finsupp.single_apply]; split_ifs <;> omega
    have hTΦ : ∀ a, T (Φ a) = S a := by
      intro a
      simp only [T, S, hΦ, Finsupp.sumElim_inl, Finsupp.sumElim_inr, K]
      rw [← hL H a, if_pos (by funext j; rw [Finsupp.single_eq_pi_single]), mul_one]
    symm
    rw [← Finset.sum_congr rfl (fun a _ => hTΦ a), ← Finset.sum_map _ Φ T]
    apply Finset.sum_subset
    · intro m hm
      rw [Finset.mem_map] at hm
      obtain ⟨a, ha, rfl⟩ := hm
      exact hmemi a ha
    · intro m hm hnot
      have hne : (fun j => m (Sum.inr j)) ≠ Pi.single i 1 := by
        intro heq
        apply hnot
        rw [Finset.mem_map]
        refine ⟨Finsupp.equivFunOnFinite.symm (fun j => m (Sum.inl j)), ?_, ?_⟩
        · rw [MvFormalGroup.HBI.mem_Iic_iff hN1] at hm ⊢
          intro j
          rw [Finsupp.coe_equivFunOnFinite_symm]
          exact hm (Sum.inl j)
        · ext s
          rcases s with j | j
          · rw [hΦ, Finsupp.sumElim_inl, Finsupp.coe_equivFunOnFinite_symm]
          · rw [hΦ, Finsupp.sumElim_inr, Finsupp.single_eq_pi_single]
            exact (congrFun heq j).symm
      simp only [T]
      rw [if_neg hne, mul_zero, smul_zero]

end S_MvFormalGroup_cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate
end P2MW
export P2MW.S_MvFormalGroup_cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate (solution)
