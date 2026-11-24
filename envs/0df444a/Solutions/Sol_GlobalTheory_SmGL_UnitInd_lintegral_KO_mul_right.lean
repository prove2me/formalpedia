-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.lintegral_KO_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:42:31.472131+00:00
-- url     : https://prove2.me/submissions/0684c992-7e9f-4ffa-b374-f57d9413bc36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_lintegral_average
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_indicator_congr_iff
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_unip_mul_levi_mem_KO
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_exists_iwasawa
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isLocallyConstant_modulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_modulus_mul_inv
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isMulRightInvariant_map
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_continuous_conj
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_haar_conj_eq_modulus_mul
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_isHaarMeasure_map
import Theorems.Thm_GlobalTheory_SmGL_coe_mem_unipRad
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviEmb
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad
import Theorems.Thm_GlobalTheory_SmGL_modulus_pos
import Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (μ : Measure (GL n k)) [μ.IsHaarMeasure] {φ : GL n k → ℝ≥0∞} (hφ : Measurable φ)
    (hlaw : ∀ (p : parab k e) x, φ (p * x) = ENNReal.ofReal (modulus k m (leviProj k e p)) * φ x) (g : GL n k) :
    ∫⁻ x in (KO k n : Set (GL n k)), φ (x * g) ∂μ = ∫⁻ x in (KO k n : Set (GL n k)), φ x ∂μ := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  obtain ⟨ν, _, _⟩ : ∃ ν : Measure (unipRad k e), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant :=
    ⟨_, isHaarMeasure_map e Measure.addHaar, isMulRightInvariant_map e Measure.addHaar⟩
  let τ : Measure (Levi k m) := Measure.pi fun _ => Measure.haar
  let N₀ : Set (unipRad k e) := Subtype.val ⁻¹' (KO k n : Set (GL n k))
  let M₀ : Set (Levi k m) := Set.univ.pi fun a => (KO k (m a) : Set (GL (m a) k))
  have hK : MeasurableSet (KO k n : Set (GL n k)) := isOpen_KO.measurableSet
  have hN₀ : IsOpen N₀ := isOpen_KO.preimage continuous_subtype_val
  have hM₀ : IsOpen M₀ := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_KO
  have hNc : IsCompact N₀ := by
    have : IsClosed (unipRad k e : Set (GL n k)) := by
      have h : (unipRad k e : Set (GL n k)) = (⋂ (i) (j) (_ : blk e j < blk e i), {g | g.val i j = 0}) ∩
          ⋂ (a) (i) (j), {g | g.val (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
        ext g
        simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      rw [h]
      refine IsClosed.inter ?_ ?_ <;>
        exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const
    exact this.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_KO
  have hMc : IsCompact M₀ := isCompact_univ_pi fun _ => isCompact_KO
  have hc0 : ν N₀ * τ M₀ ≠ 0 := mul_ne_zero (hN₀.measure_pos ν ⟨1, one_mem (KO k n)⟩).ne'
    (hM₀.measure_pos τ ⟨1, fun a _ => one_mem (KO k (m a))⟩).ne'
  have hc1 : ν N₀ * τ M₀ ≠ ⊤ := ENNReal.mul_ne_top hNc.measure_lt_top.ne hMc.measure_lt_top.ne
  let j : Levi k m × unipRad k e → GL n k := fun y => y.2 * leviEmb k e y.1
  have hj : Measurable j := ((continuous_subtype_val.comp continuous_snd).mul
    ((continuous_leviEmb k e).comp continuous_fst)).measurable
  let δ : Levi k m × unipRad k e → ℝ≥0∞ := fun y => ENNReal.ofReal (modulus k m y.1⁻¹)
  have hδ : Measurable δ := ((isLocallyConstant_modulus (k := k) (m := m)).continuous.comp
    continuous_fst.inv).measurable.ennreal_ofReal
  have mK : Measurable ((KO k n : Set (GL n k)).indicator (1 : GL n k → ℝ≥0∞)) := measurable_one.indicator hK
  have ha : ∀ x, ∫⁻ y, (KO k n : Set (GL n k)).indicator 1 (j y * x) ∂(τ.prod ν) = ν N₀ * τ M₀ := by
    intro x
    obtain ⟨u, t, w, hw, rfl⟩ := exists_iwasawa e x
    rw [lintegral_prod (fun y => (KO k n : Set (GL n k)).indicator 1 (j y * (u * leviEmb k e t * w)))
      (mK.comp (hj.mul_const _)).aemeasurable, ← measure_preimage_mul_right τ t M₀,
      ← lintegral_indicator_const (measurable_mul_const t hM₀.measurableSet)]
    refine lintegral_congr fun s => ?_
    have h : ∀ v : unipRad k e, j (s, v) * (u * leviEmb k e t * w) ∈ (KO k n : Set (GL n k)) ↔
        v * conj e s u ∈ N₀ ∧ s * t ∈ M₀ := fun v => by
      have : j (s, v) * (u * leviEmb k e t * w) = (v * conj e s u : unipRad k e) * leviEmb k e (s * t) * w := by
        simp [j, conj, mul_assoc]
      rw [this, SetLike.mem_coe, mul_mem_cancel_right hw, unip_mul_levi_mem_KO]
      simp [N₀, M₀]
    by_cases hs : s * t ∈ M₀
    · rw [Set.indicator_of_mem (show s ∈ (· * t) ⁻¹' M₀ from hs), ← measure_preimage_mul_right ν (conj e s u) N₀,
        ← lintegral_indicator_one (measurable_mul_const _ hN₀.measurableSet)]
      refine lintegral_congr fun v => ?_
      exact indicator_congr_iff ((h v).trans (and_iff_left hs)) rfl
    · rw [Set.indicator_of_notMem (show s ∉ (· * t) ⁻¹' M₀ from hs)]
      simp [Set.indicator, h, hs]
  have hb : ∀ x, ∫⁻ y, (KO k n : Set (GL n k)).indicator 1 ((j y)⁻¹ * x) * δ y ∂(τ.prod ν) = ν N₀ * τ M₀ := by
    intro x
    obtain ⟨u, t, w, hw, rfl⟩ := exists_iwasawa e x
    rw [lintegral_prod (fun y => (KO k n : Set (GL n k)).indicator 1 ((j y)⁻¹ * (u * leviEmb k e t * w)) * δ y)
      ((mK.comp (hj.inv.mul_const _)).mul hδ).aemeasurable, ← measure_preimage_mul τ t⁻¹ M₀,
      ← lintegral_indicator_const (measurable_const_mul t⁻¹ hM₀.measurableSet)]
    refine lintegral_congr fun s => ?_
    let T : Set (unipRad k e) := {u | ∃ v ∈ N₀, (u : GL n k) = leviEmb k e s * (v : GL n k) * (leviEmb k e s)⁻¹}
    have hT : T = conj e s⁻¹ ⁻¹' N₀ := by
      ext v
      refine ⟨?_, fun h => ⟨_, h, by simp [conj, mul_assoc]⟩⟩
      rintro ⟨v', hv, h⟩
      simpa [N₀, conj, h, mul_assoc] using hv
    have hTm : MeasurableSet T := hT ▸ (continuous_conj e s⁻¹).measurable hN₀.measurableSet
    have h : ∀ v : unipRad k e, (j (s, v))⁻¹ * (u * leviEmb k e t * w) ∈ (KO k n : Set (GL n k)) ↔
        u⁻¹ * v ∈ T ∧ t⁻¹ * s ∈ M₀ := fun v => by
      have : (j (s, v))⁻¹ * (u * leviEmb k e t * w) =
          ((conj e s⁻¹ (u⁻¹ * v))⁻¹ : unipRad k e) * leviEmb k e (t⁻¹ * s)⁻¹ * w := by
        simp [j, conj, mul_assoc]
      rw [this, SetLike.mem_coe, mul_mem_cancel_right hw, unip_mul_levi_mem_KO, hT, Subgroup.coe_inv, inv_mem_iff]
      simp only [Pi.inv_apply, inv_mem_iff]
      simp [N₀, M₀]
    by_cases hs : t⁻¹ * s ∈ M₀
    · have h1 : ν N₀ = ν T * ENNReal.ofReal (modulus k m s⁻¹) := by
        rw [haar_conj_eq_modulus_mul k α n m e ν s N₀ hN₀.measurableSet, mul_right_comm,
          ← ENNReal.ofReal_mul (modulus_pos k _).le, modulus_mul_inv]
        simp
      rw [Set.indicator_of_mem (show s ∈ (t⁻¹ * ·) ⁻¹' M₀ from hs), h1, ← measure_preimage_mul ν u⁻¹ T,
        ← lintegral_indicator_one (measurable_const_mul _ hTm),
        ← lintegral_mul_const _ (measurable_one.indicator (measurable_const_mul _ hTm))]
      refine lintegral_congr fun v => ?_
      exact congrArg₂ _ (indicator_congr_iff ((h v).trans (and_iff_left hs)) rfl) rfl
    · rw [Set.indicator_of_notMem (show s ∉ (t⁻¹ * ·) ⁻¹' M₀ from hs)]
      simp [Set.indicator, h, hs, -_root_.mul_inv_rev]
  have hL : MeasurableSet ((· * g⁻¹) ⁻¹' (KO k n : Set (GL n k))) := measurable_mul_const _ hK
  have key := lintegral_average μ (τ.prod ν) hK hL hj hδ hφ (c := ν N₀ * τ M₀) (fun y x => by
    let p : parab k e := ⟨y.2, unipRad_le_parab k e y.2.2⟩ * ⟨_, leviEmb_mem_parab k e y.1⟩
    have hp : leviProj k e p = y.1 := by
      rw [map_mul, (coe_mem_unipRad k _).1 y.2.2, leviProj_leviEmb, one_mul]
    have := hlaw p⁻¹ x
    rwa [map_inv, hp] at this) (fun x => by
      rw [← ha (x * g⁻¹)]
      refine lintegral_congr fun y => ?_
      exact indicator_congr_iff (by rw [Set.mem_preimage, mul_assoc]) rfl) hb
  rw [(ENNReal.mul_right_inj hc0 hc1).1 key, ← lintegral_indicator hK, ← lintegral_indicator hL,
    ← lintegral_mul_right_eq_self _ g⁻¹]
  refine lintegral_congr fun x => indicator_congr_iff Iff.rfl ?_
  rw [inv_mul_cancel_right]
end GlobalTheory.SmGL.UnitInd
