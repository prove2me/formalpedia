-- Prove2me | solution 1 for MasulloGRH.tateArchimedeanDomain_relCompact_and_interior_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:30:52.542865+00:00
-- url     : https://prove2.me/submissions/87395e9d-13fd-4050-8e76-a7f06c34ff2a

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain
import Theorems.Thm_RiemannMasullo_infiniteIdeleLog_proper
import Theorems.Thm_RiemannMasullo_infiniteIdeleLog_surjective
import Theorems.Thm_RiemannMasullo_infiniteIdeleLog_sum_zero
import Theorems.Thm_RiemannMasullo_infiniteIdeleLog_continuous
import Theorems.Thm_RiemannMasullo_infiniteIdeleNorm_ker_closed
import Theorems.Thm_RiemannMasullo_regulatorParallelotope_precompact
import Theorems.Thm_RiemannMasullo_regulatorParallelotope_interior
import Theorems.Thm_RiemannMasullo_inTorsionSector_real

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tateArchimedeanDomain_relCompact_and_interior_nonempty

open RiemannMasullo MasulloGRH NumberField.Units.dirichletUnitTheorem InfinitePlace.Completion
open scoped Classical

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- Restore the omitted coordinate of a vector of `logSpace F` so that the coordinates sum to
zero. -/
def extend (x : logSpace F) (w : InfinitePlace F) : ℝ :=
  if hw : w = w₀ then -∑ v, x v else x ⟨w, hw⟩

theorem continuous_extend : Continuous (extend F) := by
  apply continuous_pi
  intro w
  by_cases hw : w = w₀
  · simp only [extend, dif_pos hw]
    exact (continuous_finsetSum Finset.univ fun v _ ↦ continuous_apply v).neg
  · simp only [extend, dif_neg hw]
    exact continuous_apply (⟨w, hw⟩ : {v : InfinitePlace F // v ≠ w₀})

theorem extend_apply_ne (x : logSpace F) (v : {w : InfinitePlace F // w ≠ w₀}) :
    extend F x v.val = x v := dif_neg v.property

theorem sum_extend (x : logSpace F) : ∑ v, extend F x v = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  simp only [extend_apply_ne]
  simp [extend]

/-- The full logarithm of a norm-one idele is the sum-zero extension of its truncated
logarithm. -/
theorem infiniteIdeleLog_eq_extend (g : MonoidHom.ker (infiniteIdeleNorm F)) :
    infiniteIdeleLog F g.val =
      extend F (fun w : {w : InfinitePlace F // w ≠ w₀} ↦ infiniteIdeleLog F g.val w.val) := by
  funext w
  by_cases hw : w = w₀
  · subst w
    have hsum := infiniteIdeleLog_sum_zero F g
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hsum
    simpa only [extend, dite_true] using hsum
  · simp only [extend, dif_neg hw]

/-- Compact closure of `E₀` in the norm-one group. -/
theorem relCompact
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) :
    IsCompact (closure (tateArchimedeanDomain F b v₀ σ)) := by
  have hCompact := (infiniteIdeleLog_proper F).isCompact_preimage
    ((regulatorParallelotope_precompact F b).image (continuous_extend F))
  refine ((infiniteIdeleNorm_ker_closed F).isClosedEmbedding_subtypeVal.isCompact_preimage
    hCompact).closure_of_subset ?_
  intro g hg
  exact ⟨fun w ↦ infiniteIdeleLog F g.val w.val, subset_closure hg.1,
    (infiniteIdeleLog_eq_extend F g).symm⟩

/-- At every positive radius there is a point in an open subset of the local torsion sector. -/
theorem exists_open_torsionSector_at_radius (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    {a : ℝ} (ha : 0 < a) :
    ∃ U : Set v₀.Completion, IsOpen U ∧
      (∀ x : v₀.Completionˣ, x.val ∈ U → inTorsionSector F v₀ σ x) ∧
      ∃ z ∈ U, ‖z‖ = a := by
  by_cases hv : v₀.IsReal
  · let U := extensionEmbeddingOfIsReal hv ⁻¹' Set.Ioi (0 : ℝ)
    obtain ⟨z, hz⟩ := surjective_extensionEmbeddingOfIsReal hv a
    refine ⟨U, isOpen_Ioi.preimage (isometry_extensionEmbeddingOfIsReal hv).continuous,
      fun x hx ↦ (inTorsionSector_real F v₀ σ hv x).mpr hx, z, ?_, ?_⟩
    · change 0 < extensionEmbeddingOfIsReal hv z
      rwa [hz]
    · rw [← (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) z,
        hz, Real.norm_of_nonneg ha.le]
  · let f (z : v₀.Completion) := σ (extensionEmbedding v₀ z)
    have hσ : Isometry σ := by
      change Isometry (σ.toAlgHom : ℂ → ℂ)
      rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
      · rw [h]
        exact isometry_id
      · rw [h]
        exact Complex.isometry_conj
    have hf : Isometry f := hσ.comp (isometry_extensionEmbedding v₀)
    let bound := 2 * Real.pi / (Units.torsionOrder F : ℝ)
    have hbound : 0 < bound := div_pos Real.two_pi_pos (by exact_mod_cast Units.torsionOrder_pos F)
    let θ := min bound Real.pi / 2
    have hθ : 0 < θ := half_pos (lt_min hbound Real.pi_pos)
    have hθb : θ < bound := (half_lt_self (lt_min hbound Real.pi_pos)).trans_le (min_le_left _ _)
    have hθπ : θ < Real.pi := (half_lt_self (lt_min hbound Real.pi_pos)).trans_le (min_le_right _ _)
    let w : ℂ := (a : ℂ) * Complex.exp (θ * Complex.I)
    have harg : w.arg = θ := by
      change Complex.arg ((a : ℂ) * Complex.exp (θ * Complex.I)) = θ
      rw [Complex.arg_real_mul _ ha, Complex.arg_exp_mul_I]
      apply (toIocMod_eq_self Real.two_pi_pos).mpr
      exact ⟨by linarith [Real.pi_pos], by linarith⟩
    have hwnorm : ‖w‖ = a := by
      change ‖(a : ℂ) * Complex.exp (θ * Complex.I)‖ = a
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    obtain ⟨z, hz⟩ := (σ.surjective.comp (surjective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hv))) w
    change f z = w at hz
    let V : Set ℂ := Complex.slitPlane ∩ Complex.arg ⁻¹' Set.Ioo 0 bound
    refine ⟨f ⁻¹' V, (Complex.continuousOn_arg.isOpen_inter_preimage Complex.isOpen_slitPlane
      isOpen_Ioo).preimage hf.continuous, ?_, z, ?_, ?_⟩
    · intro x hx
      exact Set.Ioo_subset_Ico_self hx.2
    · change f z ∈ V
      rw [hz]
      refine ⟨Complex.mem_slitPlane_iff_arg.mpr
        ⟨harg.trans_ne hθπ.ne, norm_ne_zero_iff.mp (hwnorm.trans_ne ha.ne')⟩, ?_⟩
      change w.arg ∈ Set.Ioo 0 bound
      rw [harg]
      exact ⟨hθ, hθb⟩
    · rw [← hf.norm_map_of_map_zero (by simp [f]) z, hz, hwnorm]

/-- An archimedean idele whose logarithms sum to zero has norm one. -/
theorem infiniteIdeleNorm_eq_one_of_sum_log (g : (InfiniteAdeleRing F)ˣ)
    (hsum : ∑ v, infiniteIdeleLog F g v = 0) : infiniteIdeleNorm F g = 1 := by
  apply Units.ext
  apply NNReal.coe_injective
  have hne (v : InfinitePlace F) : g.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g).ne_zero
  simp only [infiniteIdeleNorm, Units.val_one, NNReal.coe_one, MonoidHom.finsetProd_apply,
    MonoidHom.pow_apply, MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val,
    NNReal.coe_prod, NNReal.coe_pow]
  change ∏ v : InfinitePlace F, ‖g.val v‖ ^ v.mult = 1
  calc
    ∏ v : InfinitePlace F, ‖g.val v‖ ^ v.mult = ∏ v, Real.exp (infiniteIdeleLog F g v) := by
      apply Finset.prod_congr rfl
      intro v _
      rw [infiniteIdeleLog, Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr (hne v))]
    _ = 1 := by rw [← Real.exp_sum, hsum, Real.exp_zero]

/-- Non-empty interior of `E₀` in the norm-one group. -/
theorem interior_nonempty
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) :
    (interior (tateArchimedeanDomain F b v₀ σ)).Nonempty := by
  obtain ⟨x, hx⟩ := regulatorParallelotope_interior F b
  obtain ⟨a, ha⟩ := infiniteIdeleLog_surjective F (extend F x)
  obtain ⟨U, hU, hsector, z, hz, hznorm⟩ :=
    exists_open_torsionSector_at_radius F v₀ σ (Real.exp_pos (extend F x v₀ / v₀.mult))
  have hzne : z ≠ 0 := norm_ne_zero_iff.mp (hznorm.trans_ne (Real.exp_pos _).ne')
  -- Replace the chosen component with a point of the same logarithmic radius.
  let localUnits := Function.update (MulEquiv.piUnits a) v₀ (Units.mk0 z hzne)
  let g : (InfiniteAdeleRing F)ˣ := MulEquiv.piUnits.symm localUnits
  have hg₀ : g.val v₀ = z := by
    change (localUnits v₀).val = z
    simp [localUnits]
  have hlog : infiniteIdeleLog F g = extend F x := by
    funext v
    by_cases hv : v = v₀
    · subst v
      rw [infiniteIdeleLog, hg₀, hznorm, Real.log_exp, mul_div_cancel₀ _ v₀.mult_coe_ne_zero]
    · change (v.mult : ℝ) * Real.log
        ‖(Function.update (MulEquiv.piUnits a) v₀ (Units.mk0 z hzne) v).val‖ = extend F x v
      rw [Function.update_of_ne hv]
      exact congrFun ha v
  have hnorm : infiniteIdeleNorm F g = 1 :=
    infiniteIdeleNorm_eq_one_of_sum_log F g (by rw [hlog]; exact sum_extend F x)
  let p (u : MonoidHom.ker (infiniteIdeleNorm F)) : logSpace F :=
    fun v ↦ infiniteIdeleLog F u.val v.val
  let q (u : MonoidHom.ker (infiniteIdeleNorm F)) : v₀.Completion := u.val.val v₀
  have hp : Continuous p := continuous_pi fun v ↦
    (continuous_apply v.val).comp ((infiniteIdeleLog_continuous F).comp continuous_subtype_val)
  have hval : Continuous (fun u : (InfiniteAdeleRing F)ˣ ↦ (u : InfiniteAdeleRing F)) :=
    Units.continuous_val
  have heval : Continuous (fun y : InfiniteAdeleRing F ↦ y v₀) := continuous_apply v₀
  have hq : Continuous q := heval.comp (hval.comp continuous_subtype_val)
  have hSubset : (p ⁻¹' interior (regulatorParallelotope F b)) ∩ (q ⁻¹' U) ⊆
      tateArchimedeanDomain F b v₀ σ :=
    fun u hu ↦ ⟨(interior_subset hu.1 : p u ∈ regulatorParallelotope F b), hsector _ hu.2⟩
  refine ⟨⟨g, hnorm⟩, interior_maximal hSubset
    ((isOpen_interior.preimage hp).inter (hU.preimage hq)) ⟨?_, ?_⟩⟩
  · change (fun v : {w : InfinitePlace F // w ≠ w₀} ↦ infiniteIdeleLog F g v.val) ∈
      interior (regulatorParallelotope F b)
    simpa only [hlog, extend_apply_ne] using hx
  · change g.val v₀ ∈ U
    rwa [hg₀]

end

end Sol_MasulloGRH_tateArchimedeanDomain_relCompact_and_interior_nonempty

open MasulloGRH in
theorem solution
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) :
    IsCompact (closure (tateArchimedeanDomain F b v₀ σ)) ∧
    IsCompact (closure
      (Subtype.val '' tateArchimedeanDomain F b v₀ σ : Set (InfiniteAdeleRing F)ˣ)) ∧
    (interior (tateArchimedeanDomain F b v₀ σ)).Nonempty := by
  have h1 := Sol_MasulloGRH_tateArchimedeanDomain_relCompact_and_interior_nonempty.relCompact
    F b v₀ σ
  refine ⟨h1, ?_,
    Sol_MasulloGRH_tateArchimedeanDomain_relCompact_and_interior_nonempty.interior_nonempty
      F b v₀ σ⟩
  exact (h1.image continuous_subtype_val).closure_of_subset (Set.image_mono subset_closure)
