-- Prove2me | solution 1 for MasulloGRH.tateIdeleDomain_finite_translates
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T14:15:30.347437+00:00
-- url     : https://prove2.me/submissions/99483f73-a09c-4b9a-a4fa-e1b551240646

import Mathlib
import Definitions.Def_MasulloGRH_TateIdeleDomain
import Theorems.Thm_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty

open NumberField IsDedekindDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tateIdeleDomain_finite_translates

open MasulloGRH
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
/-- The norm on the completion at an infinite place restricts to the place on `F`. -/
theorem norm_algebraMap_completion (w : InfinitePlace F) (ξ : F) :
    ‖algebraMap F w.Completion ξ‖ = w ξ := by
  have h := InfinitePlace.Completion.norm_coe (v := w) ((WithAbs.equiv w.1).symm ξ)
  rw [RingEquiv.apply_symm_apply] at h
  exact h

/-- The image of an algebraic integer in the completion at a finite place is integral. -/
theorem valued_algebraMap_le_one (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) x) ≤ (1 : ℤᵐ⁰) := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v x
  exact h.trans_le (v.valuation_le_one x)

/-- An element of the completion `F_v` at a finite place lies in `d⁻¹ 𝒪_v` for some nonzero
`d ∈ 𝒪_F`. -/
theorem exists_ne_zero_valued_mul_le_one (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * x) ≤ (1 : ℤᵐ⁰) := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hπv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) < (1 : ℤᵐ⁰) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v π
    exact h.trans_lt ((v.valuation_lt_one_iff_mem π).2 hπ)
  have hπn : ‖algebraMap (𝓞 F) (v.adicCompletion F) π‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr hπv
  have hpos : (0 : ℝ) < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) hπn
  refine ⟨π ^ n, pow_ne_zero n hπ0, ?_⟩
  rw [← Valued.toNormedField.norm_le_one_iff, map_pow, norm_mul, norm_pow]
  calc ‖algebraMap (𝓞 F) (v.adicCompletion F) π‖ ^ n * ‖x‖
      ≤ (max ‖x‖ 1)⁻¹ * max ‖x‖ 1 :=
        mul_le_mul hn.le (le_max_left _ _) (norm_nonneg _) (inv_pos.mpr hpos).le
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- **Clearing denominators**: for every finite adele `a` there is a nonzero `d ∈ 𝒪_F` such that
`d a` is integral at every finite place. -/
theorem exists_ne_zero_forall_valued_mul_le_one (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * a v) ≤ (1 : ℤᵐ⁰) := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ a v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose dv hdv0 hdv using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_ne_zero_valued_mul_le_one v (a v)
  refine ⟨∏ v ∈ hfin.toFinset, dv v, Finset.prod_ne_zero_iff.mpr fun v _ => hdv0 v, fun v => ?_⟩
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, map_mul (algebraMap (𝓞 F) (v.adicCompletion F)),
      mul_right_comm, map_mul]
    exact mul_le_one' (hdv v) (valued_algebraMap_le_one v _)
  · have hav : a v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr h)
    rw [map_mul]
    exact mul_le_one' (valued_algebraMap_le_one v _)
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hav)

/-- The finite adeles that are integral at every place form an open set. -/
lemma isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

/-- For `d ∈ 𝒪_F`, the ideles `g` such that `d g` is integral at every finite place form an open
subset of the idele group. -/
lemma isOpen_denominatorSet (d : 𝓞 F) :
    IsOpen {g : IdeleGroup F | ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * (g : AdeleRing (𝓞 F) F).2 v) ≤
        (1 : ℤᵐ⁰)} := by
  have hc : Continuous (fun g : IdeleGroup F =>
      algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d * (g : AdeleRing (𝓞 F) F).2) :=
    continuous_const.mul (continuous_snd.comp Units.continuous_val)
  have h := (isOpen_integral (F := F)).preimage hc
  convert h using 1
  ext g
  refine forall_congr' fun v => ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rfl

/-- **Discreteness of `Fˣ` in the idele group**: a compact subset of `GL₁(𝔸_F)` contains only
finitely many principal ideles. -/
theorem finite_principal_mem_of_isCompact (Q : Set (IdeleGroup F)) (hQ : IsCompact Q) :
    {ξ : Fˣ | principalIdele F ξ ∈ Q}.Finite := by
  classical
  -- a common denominator for the finite components of the elements of `Q`
  have hcover : Q ⊆ ⋃ d : {d : 𝓞 F // d ≠ 0}, {g : IdeleGroup F |
      ∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d.1 * (g : AdeleRing (𝓞 F) F).2 v) ≤
          (1 : ℤᵐ⁰)} := by
    intro g _
    obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_valued_mul_le_one (g : AdeleRing (𝓞 F) F).2
    exact Set.mem_iUnion.mpr ⟨⟨d, hd0⟩, hd⟩
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover _ (fun d : {d : 𝓞 F // d ≠ 0} =>
    isOpen_denominatorSet (F := F) d.1) hcover
  let D : 𝓞 F := ∏ i ∈ t, i.1
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => i.2
  have hDF : (algebraMap (𝓞 F) F D) ≠ 0 := by
    simpa using hD0
  have hDQ : ∀ g ∈ Q, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D * (g : AdeleRing (𝓞 F) F).2 v) ≤
        (1 : ℤᵐ⁰) := by
    intro g hg v
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hg)
    obtain ⟨hit, hgi⟩ := Set.mem_iUnion.mp hi
    have hprod : D = i.1 * ∏ j ∈ t.erase i, j.1 := (Finset.mul_prod_erase _ _ hit).symm
    rw [hprod, map_mul (algebraMap (𝓞 F) (v.adicCompletion F)), mul_right_comm, map_mul]
    exact mul_le_one' (hgi v) (valued_algebraMap_le_one v _)
  -- bounded archimedean absolute values
  have h2 : ∀ w : InfinitePlace F, ∃ C : ℝ, ∀ g ∈ Q, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ≤ C := by
    intro w
    have hc : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).1 w) :=
      (continuous_apply w).comp (continuous_fst.comp Units.continuous_val)
    obtain ⟨C, hC⟩ := (hQ.image hc).isBounded.exists_norm_le
    exact ⟨C, fun g hg ↦ hC _ ⟨g, hg, rfl⟩⟩
  choose C hC using h2
  let B : ℝ := ∑ w : InfinitePlace F, w (algebraMap (𝓞 F) F D) * C w
  have hfin := Embeddings.finite_of_norm_le F ℂ B
  have hinj : Set.InjOn (fun ξ : Fˣ ↦ algebraMap (𝓞 F) F D * (ξ : F))
      ((fun ξ : Fˣ ↦ algebraMap (𝓞 F) F D * (ξ : F)) ⁻¹'
        {x : F | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ B}) :=
    ((mul_right_injective₀ hDF).comp Units.val_injective).injOn
  refine (hfin.preimage hinj).subset ?_
  intro ξ hξQ
  have hξQ' : principalIdele F ξ ∈ Q := hξQ
  have hnonneg : ∀ w : InfinitePlace F, 0 ≤ w (algebraMap (𝓞 F) F D) * C w := by
    intro w
    have h := hC w _ hξQ'
    exact mul_nonneg (apply_nonneg _ _) ((norm_nonneg _).trans h)
  refine ⟨?_, fun φ ↦ ?_⟩
  · -- `D ξ` is integral at every finite place
    have hmem : algebraMap (𝓞 F) F D * (ξ : F) ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v ↦ ?_
      have h := hDQ _ hξQ' v
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      have e : ((algebraMap (𝓞 F) F D * (ξ : F) : F) : v.adicCompletion F) =
          algebraMap (𝓞 F) (v.adicCompletion F) D *
            ((principalIdele F ξ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v := by
        change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D * (ξ : F)) =
          algebraMap (𝓞 F) (v.adicCompletion F) D * algebraMap F (v.adicCompletion F) (ξ : F)
        rw [map_mul, ← IsScalarTower.algebraMap_apply]
      rw [e]
      exact h
    obtain ⟨z, hz⟩ := hmem
    change IsIntegral ℤ (algebraMap (𝓞 F) F D * (ξ : F))
    rw [← hz]
    exact z.isIntegral_coe
  · -- the archimedean absolute values of `D ξ` are bounded
    have h := hC (InfinitePlace.mk φ) _ hξQ'
    have h' : (InfinitePlace.mk φ) (ξ : F) ≤ C (InfinitePlace.mk φ) := by
      rw [← norm_algebraMap_completion]
      exact h
    calc ‖φ (algebraMap (𝓞 F) F D * (ξ : F))‖
        = (InfinitePlace.mk φ) (algebraMap (𝓞 F) F D) * (InfinitePlace.mk φ) (ξ : F) := by
          rw [← InfinitePlace.apply, map_mul]
      _ ≤ (InfinitePlace.mk φ) (algebraMap (𝓞 F) F D) * C (InfinitePlace.mk φ) :=
          mul_le_mul_of_nonneg_left h' (apply_nonneg _ _)
      _ ≤ B := Finset.single_le_sum (f := fun w : InfinitePlace F ↦
            w (algebraMap (𝓞 F) F D) * C w) (fun w _ ↦ hnonneg w) (Finset.mem_univ _)

end Sol_MasulloGRH_tateIdeleDomain_finite_translates

open MasulloGRH
open Sol_MasulloGRH_tateIdeleDomain_finite_translates

theorem solution
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hr₁ : r 1 = 1) (hrn : ∀ c : ClassGroup (𝓞 F), ideleNorm (r c) = 1)
    (hr : ∀ c : ClassGroup (𝓞 F), ideleIdealClass F (r c) = c)
    (K : Set {g : IdeleGroup F // ideleNorm g = 1}) (hK : IsCompact K) :
    {ξ : Fˣ | ∃ e ∈ closure
        {g : {g : IdeleGroup F // ideleNorm g = 1} | g.val ∈ tateIdeleDomain F b v₀ σ r},
      ∃ k ∈ K, (k : IdeleGroup F) = principalIdele F ξ * (e : IdeleGroup F)}.Finite := by
  -- the closure of the fundamental domain is compact
  have hE : IsCompact (closure
      {g : {g : IdeleGroup F // ideleNorm g = 1} | g.val ∈ tateIdeleDomain F b v₀ σ r}) :=
    (tateIdeleDomain_relCompact_and_interior_nonempty F b v₀ σ r hr₁ hrn hr).2.1
  -- hence so is the set of quotients `K · (closure E)⁻¹` in the idele group
  have hc : Continuous (fun p : {g : IdeleGroup F // ideleNorm g = 1} ×
      {g : IdeleGroup F // ideleNorm g = 1} ↦ (p.1 : IdeleGroup F) * (p.2 : IdeleGroup F)⁻¹) :=
    (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd).inv
  have hQ := (hK.prod hE).image hc
  refine (finite_principal_mem_of_isCompact _ hQ).subset ?_
  rintro ξ ⟨e, he, k, hk, hke⟩
  exact ⟨(k, e), ⟨hk, he⟩, by
    change (k : IdeleGroup F) * (e : IdeleGroup F)⁻¹ = principalIdele F ξ
    rw [hke, mul_inv_cancel_right]⟩
