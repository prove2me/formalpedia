-- Prove2me | solution 1 for NumberField.AdelicFourier.integrable_mul_of_continuous_of_decay_of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8809ed98-d010-5beb-92da-8ced112658dc

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant.NumberField IsDedekindDomain MeasureTheory"
open scoped Classical

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant.NumberField IsDedekindDomain MeasureTheory NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant.NumberField.AdelicFourier NumberField.InfiniteAdeleRing Filter"
open TopologicalSpace

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing InfinitePlace.not_isReal_iff_isComplex mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace mixedEmbedding.latticeBasis InfinitePlace AdeleRing AdelicBox.continuous_ringEquiv_mixedSpace AdelicBox.properSpace_completion AdelicBox.norm_apply_le_of_isReal AdelicBox.norm_apply_le_of_isComplex"
namespace AdelicFourier
namespace C8DecayInt
p2m_open "NumberField.AdelicFourier NumberField"

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "E∞" => mixedEmbedding.mixedSpace F

section Cells

open scoped Classical

def mixedCell : Set E∞ := closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))

theorem isCompact_mixedCell : IsCompact (mixedCell F) :=
  (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).isCompact_closure

theorem isClosed_mixedCell : IsClosed (mixedCell F) := isClosed_closure

theorem exists_norm_le_of_mem_mixedCell : ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ mixedCell F, ‖q‖ ≤ R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (isCompact_mixedCell F).isBounded
  exact ⟨max R 0, le_max_right _ _, fun q hq => (hR q hq).trans (le_max_left _ _)⟩

def archCell : Set (InfiniteAdeleRing F) := ringEquiv_mixedSpace F ⁻¹' mixedCell F

theorem isCompact_archCell : IsCompact (archCell F) := by
  obtain ⟨R, -, hR⟩ := exists_norm_le_of_mem_mixedCell F
  haveI : ∀ v : InfinitePlace F, ProperSpace v.Completion := fun v => AdelicBox.properSpace_completion F v
  have hbig : IsCompact {x : InfiniteAdeleRing F | ∀ v, ‖x v‖ ≤ R} := by
    have : {x : InfiniteAdeleRing F | ∀ v, ‖x v‖ ≤ R} =
        Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) R := by
      ext x
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_closedBall _ _
  refine hbig.of_isClosed_subset ((isClosed_mixedCell F).preimage (AdelicBox.continuous_ringEquiv_mixedSpace F)) ?_
  intro x hx v
  have hx' : ‖ringEquiv_mixedSpace F x‖ ≤ R := hR _ hx
  by_cases hv : v.IsReal
  · exact (AdelicBox.norm_apply_le_of_isReal F x hv).trans hx'
  · exact (AdelicBox.norm_apply_le_of_isComplex F x (InfinitePlace.not_isReal_iff_isComplex.mp hv)).trans hx'

variable {F}

def cell0 (K : Set (FiniteAdeleRing (𝓞 F) F)) : Set 𝔸 := {x | x.1 ∈ archCell F ∧ x.2 ∈ K}

theorem isCompact_cell0 {K : Set (FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K) : IsCompact (cell0 K) := by
  have : IsCompact (archCell F ×ˢ K) := (isCompact_archCell F).prod hK
  exact this

def cellShift (l : E∞) : 𝔸 := ((ringEquiv_mixedSpace F).symm l, (0 : FiniteAdeleRing (𝓞 F) F))

def cell (K : Set (FiniteAdeleRing (𝓞 F) F)) (l : E∞) : Set 𝔸 := (fun z : 𝔸 => -cellShift l + z) ⁻¹' cell0 K

theorem isCompact_cell {K : Set (FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K) (l : E∞) : IsCompact (cell K l) :=
  (Homeomorph.addLeft (-cellShift l)).isCompact_preimage.mpr (isCompact_cell0 hK)

theorem mem_cell_iff {K : Set (FiniteAdeleRing (𝓞 F) F)} {l : E∞} {x : 𝔸} :
    x ∈ cell K l ↔ ringEquiv_mixedSpace F x.1 - l ∈ mixedCell F ∧ x.2 ∈ K := by
  show (-cellShift l + x).1 ∈ archCell F ∧ (-cellShift l + x).2 ∈ K ↔ _
  have h1 : (-cellShift l + x).1 = -(ringEquiv_mixedSpace F).symm l + x.1 := rfl
  have h2 : (-cellShift l + x).2 = -0 + x.2 := rfl
  rw [h2, neg_zero, zero_add, h1]
  simp only [archCell, Set.mem_preimage, map_add, map_neg, RingEquiv.apply_symm_apply]
  rw [neg_add_eq_sub]

theorem mem_cell_floor {K : Set (FiniteAdeleRing (𝓞 F) F)} {x : 𝔸} (hx : x.2 ∈ K) :
    x ∈ cell K (ZSpan.floor (mixedEmbedding.latticeBasis F) (ringEquiv_mixedSpace F x.1) : E∞) := by
  rw [mem_cell_iff]
  refine ⟨subset_closure ?_, hx⟩
  rw [← ZSpan.fract_apply]
  exact ZSpan.fract_mem_fundamentalDomain _ _

theorem measure_cell [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddLeftInvariant]
    (K : Set (FiniteAdeleRing (𝓞 F) F)) (l : E∞) : μ (cell K l) = μ (cell0 K) :=
  measure_preimage_add μ _ _

end Cells

end NumberField.AdelicFourier.C8DecayInt

end

open NumberField.AdelicFourier.C8DecayInt in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (G : mixedEmbedding.mixedSpace F → ℂ) (hG : Continuous G)
    (k : ℕ) (hk : Module.finrank ℝ (mixedEmbedding.mixedSpace F) < k)
    (C : ℝ) (hdecay : ∀ y : mixedEmbedding.mixedSpace F, (1 + ‖y‖) ^ k * ‖G y‖ ≤ C)
    (H : FiniteAdeleRing (𝓞 F) F → ℂ) (hH : IsLocallyConstant H) (hHc : HasCompactSupport H) :
    Integrable (fun x : AdeleRing (𝓞 F) F => G (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * H x.2) μ := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he
  have hcont : Continuous fun x : AdeleRing (𝓞 F) F => G (e x.1) * H x.2 :=
    (hG.comp ((AdelicBox.continuous_ringEquiv_mixedSpace F).comp continuous_fst)).mul
      (hH.continuous.comp continuous_snd)
  set f : C(AdeleRing (𝓞 F) F, ℂ) := ⟨fun x => G (e x.1) * H x.2, hcont⟩ with hf
  set K := tsupport H with hKdef
  have hK : IsCompact K := hHc
  set b := mixedEmbedding.latticeBasis F with hb
  let L : Submodule ℤ (mixedEmbedding.mixedSpace F) := Submodule.span ℤ (Set.range b)
  let s : L → Compacts (AdeleRing (𝓞 F) F) := fun l => ⟨cell K (l : mixedEmbedding.mixedSpace F), isCompact_cell hK _⟩
  have hkL : Module.finrank ℤ L < k := by rw [ZLattice.rank ℝ L]; exact hk
  obtain ⟨R, hR0, hR⟩ := exists_norm_le_of_mem_mixedCell F
  obtain ⟨B, hB⟩ := hHc.exists_bound_of_continuous hH.continuous
  have hC0 : 0 ≤ C := le_trans (by positivity) (hdecay 0)
  have hB0 : 0 ≤ max B 0 := le_max_right _ _

  have hsup : ∀ l : L, ‖f.restrict (s l)‖ ≤
      max B 0 * (C * (1 + R) ^ k) / (1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k := by
    intro l
    have hden : 0 < (1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k := by positivity
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ cell K (l : mixedEmbedding.mixedSpace F) := hx
    rw [mem_cell_iff] at hx'
    obtain ⟨hq, -⟩ := hx'
    have hqR : ‖e x.1 - (l : mixedEmbedding.mixedSpace F)‖ ≤ R := hR _ hq
    have hcmp : 1 + ‖(l : mixedEmbedding.mixedSpace F)‖ ≤ (1 + R) * (1 + ‖e x.1‖) := by
      have : ‖(l : mixedEmbedding.mixedSpace F)‖ ≤ ‖e x.1‖ + R := by
        calc ‖(l : mixedEmbedding.mixedSpace F)‖
            = ‖e x.1 - (e x.1 - (l : mixedEmbedding.mixedSpace F))‖ := by rw [sub_sub_cancel]
          _ ≤ ‖e x.1‖ + ‖e x.1 - (l : mixedEmbedding.mixedSpace F)‖ := norm_sub_le _ _
          _ ≤ ‖e x.1‖ + R := by gcongr
      nlinarith [norm_nonneg (e x.1), norm_nonneg (l : mixedEmbedding.mixedSpace F)]
    have hpow : (1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k ≤ (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcmp k
    have hg : ‖G (e x.1)‖ ≤ C / (1 + ‖e x.1‖) ^ k := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact hdecay _
    have hgx : ‖G (e x.1)‖ ≤ C * (1 + R) ^ k / (1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k := by
      refine hg.trans ?_
      rw [div_le_div_iff₀ (by positivity) hden]
      calc C * (1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k ≤ C * ((1 + R) ^ k * (1 + ‖e x.1‖) ^ k) :=
            mul_le_mul_of_nonneg_left hpow hC0
        _ = C * (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by ring
    show ‖G (e x.1) * H x.2‖ ≤ _
    rw [norm_mul]
    calc ‖G (e x.1)‖ * ‖H x.2‖ ≤ (C * (1 + R) ^ k / (1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k) * max B 0 :=
          mul_le_mul hgx ((hB _).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ = max B 0 * (C * (1 + R) ^ k) / (1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k := by ring

  have hμ : ∀ l : L, μ.real (s l) = μ.real (cell0 K) := fun l => by
    show μ.real (cell K (l : mixedEmbedding.mixedSpace F)) = μ.real (cell0 K)
    rw [measureReal_def, measureReal_def, measure_cell]
  have hsum : Summable fun l : L => ‖f.restrict (s l)‖ * μ.real (s l) := by
    simp_rw [hμ]
    refine Summable.mul_right _ ?_
    have hcomp : Summable fun l : L =>
        max B 0 * (C * (1 + R) ^ k) * ‖(l : mixedEmbedding.mixedSpace F) - 0‖⁻¹ ^ k :=
      (ZLattice.summable_norm_sub_inv_pow L k hkL 0).mul_left _
    refine Summable.of_norm_bounded_eventually hcomp ?_
    have hfin : {l : L | (l : mixedEmbedding.mixedSpace F) = 0}.Finite :=
      Set.Subsingleton.finite fun a ha c hc => Subtype.val_injective (ha.trans hc.symm)
    filter_upwards [hfin.compl_mem_cofinite] with l hl
    have hl0 : (l : mixedEmbedding.mixedSpace F) ≠ 0 := hl
    have hpos : 0 < ‖(l : mixedEmbedding.mixedSpace F)‖ := norm_pos_iff.mpr hl0
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (hsup l).trans ?_
    rw [sub_zero]
    have hkey : ((1 + ‖(l : mixedEmbedding.mixedSpace F)‖) ^ k)⁻¹ ≤ ‖(l : mixedEmbedding.mixedSpace F)‖⁻¹ ^ k := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hpos (le_add_of_nonneg_left zero_le_one)) k
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hB0 (by positivity))

  have hU : IntegrableOn f (⋃ l : L, (s l : Set (AdeleRing (𝓞 F) F))) μ :=
    integrableOn_iUnion_of_summable_norm_restrict hsum
  have hsupp : Function.support (fun x : AdeleRing (𝓞 F) F => G (e x.1) * H x.2)
      ⊆ ⋃ l : L, (s l : Set (AdeleRing (𝓞 F) F)) := by
    intro x hx
    have hx2 : x.2 ∈ K := by
      refine subset_tsupport _ ?_
      intro h0
      exact hx (by simp only [h0, mul_zero])
    exact Set.mem_iUnion.mpr ⟨ZSpan.floor b (e x.1), mem_cell_floor hx2⟩
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hU

end S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant
end P2MW
export P2MW.S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant (solution)
