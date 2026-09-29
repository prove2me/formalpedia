-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_integrable_forall_norm_comp_sub_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e36a5c11-f58e-5d80-93eb-ee1f5cf14998

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm

import Definitions.Def_NumberField_AdelicBox
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicFourier NumberField.InfiniteAdeleRing Filter
open TopologicalSpace
open scoped SchwartzMap

noncomputable section

namespace Ws20
namespace SBDom

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "E∞" => mixedEmbedding.mixedSpace F

open scoped Classical in

theorem exists_one_add_norm_pow_mul_norm_le (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ℕ) :
    ∃ C : ℝ, ∀ y : mixedEmbedding.mixedSpace F, (1 + ‖y‖) ^ k * ‖g y‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl g y
  rwa [norm_iteratedFDeriv_zero] at h

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

open scoped Classical in

def decayExp : ℕ :=
  Module.finrank ℤ (Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) + 1

variable {F}

theorem one_add_norm_le_mul (y v : E∞) : 1 + ‖y‖ ≤ (1 + ‖v‖) * (1 + ‖y - v‖) := by
  have : ‖y‖ ≤ ‖y - v‖ + ‖v‖ := by
    calc ‖y‖ = ‖(y - v) + v‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - v‖ + ‖v‖ := norm_add_le _ _
  nlinarith [norm_nonneg (y - v), norm_nonneg v]

open scoped Classical in

theorem integrable_of_continuous_of_decay [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    (φ : 𝔸 → ℝ) (hcont : Continuous φ) {K : Set (FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K)
    (hsupp : ∀ x : 𝔸, φ x ≠ 0 → x.2 ∈ K)
    (C : ℝ) (hC : ∀ x : 𝔸, (1 + ‖ringEquiv_mixedSpace F x.1‖) ^ decayExp F * ‖φ x‖ ≤ C) :
    Integrable φ μ := by
  set e := ringEquiv_mixedSpace F with he
  set f : C(𝔸, ℝ) := ⟨φ, hcont⟩ with hf
  set b := mixedEmbedding.latticeBasis F with hb
  let L : Submodule ℤ E∞ := Submodule.span ℤ (Set.range b)
  let s : L → Compacts 𝔸 := fun l => ⟨cell K (l : E∞), isCompact_cell hK _⟩
  obtain ⟨R, hR0, hR⟩ := exists_norm_le_of_mem_mixedCell F
  set k : ℕ := decayExp F with hk
  have hkL : Module.finrank ℤ L < k := Nat.lt_succ_self _
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)

  have hsup : ∀ l : L, ‖f.restrict (s l)‖ ≤ C * (1 + R) ^ k / (1 + ‖(l : E∞)‖) ^ k := by
    intro l
    have hden : 0 < (1 + ‖(l : E∞)‖) ^ k := by positivity
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ cell K (l : E∞) := hx
    rw [mem_cell_iff] at hx'
    obtain ⟨hq, -⟩ := hx'
    have hqR : ‖e x.1 - (l : E∞)‖ ≤ R := hR _ hq
    have hcmp : 1 + ‖(l : E∞)‖ ≤ (1 + R) * (1 + ‖e x.1‖) := by
      have : ‖(l : E∞)‖ ≤ ‖e x.1‖ + R := by
        calc ‖(l : E∞)‖ = ‖e x.1 - (e x.1 - (l : E∞))‖ := by rw [sub_sub_cancel]
          _ ≤ ‖e x.1‖ + ‖e x.1 - (l : E∞)‖ := norm_sub_le _ _
          _ ≤ ‖e x.1‖ + R := by gcongr
      nlinarith [norm_nonneg (e x.1), norm_nonneg (l : E∞)]
    have hpow : (1 + ‖(l : E∞)‖) ^ k ≤ (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcmp k
    have hφ : ‖φ x‖ ≤ C / (1 + ‖e x.1‖) ^ k := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact hC _
    show ‖φ x‖ ≤ _
    refine hφ.trans ?_
    rw [div_le_div_iff₀ (by positivity) hden]
    calc C * (1 + ‖(l : E∞)‖) ^ k ≤ C * ((1 + R) ^ k * (1 + ‖e x.1‖) ^ k) :=
          mul_le_mul_of_nonneg_left hpow hC0
      _ = C * (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by ring

  have hμ : ∀ l : L, μ.real (s l) = μ.real (cell0 K) := fun l => by
    show μ.real (cell K (l : E∞)) = μ.real (cell0 K)
    rw [measureReal_def, measureReal_def, measure_cell]
  have hsum : Summable fun l : L => ‖f.restrict (s l)‖ * μ.real (s l) := by
    simp_rw [hμ]
    refine Summable.mul_right _ ?_
    have hcomp : Summable fun l : L => C * (1 + R) ^ k * ‖(l : E∞) - 0‖⁻¹ ^ k :=
      (ZLattice.summable_norm_sub_inv_pow L k hkL 0).mul_left _
    refine Summable.of_norm_bounded_eventually hcomp ?_
    have hfin : {l : L | (l : E∞) = 0}.Finite :=
      Set.Subsingleton.finite fun a ha c hc => Subtype.val_injective (ha.trans hc.symm)
    filter_upwards [hfin.compl_mem_cofinite] with l hl
    have hl0 : (l : E∞) ≠ 0 := hl
    have hpos : 0 < ‖(l : E∞)‖ := norm_pos_iff.mpr hl0
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (hsup l).trans ?_
    rw [sub_zero]
    have hkey : ((1 + ‖(l : E∞)‖) ^ k)⁻¹ ≤ ‖(l : E∞)‖⁻¹ ^ k := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hpos (le_add_of_nonneg_left zero_le_one)) k
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hU : IntegrableOn f (⋃ l : L, (s l : Set 𝔸)) μ := integrableOn_iUnion_of_summable_norm_restrict hsum
  have hsupp' : Function.support φ ⊆ ⋃ l : L, (s l : Set 𝔸) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨ZSpan.floor b (e x.1), mem_cell_floor (hsupp x hx)⟩
  exact (integrableOn_iff_integrable_of_support_subset hsupp').mp hU

theorem exists_bound_pureTensor [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    (g : 𝓢(E∞, ℂ)) (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ bound : 𝔸 → ℝ, Integrable bound μ ∧ ∀ y : 𝔸, y.2 = 0 → ‖ringEquiv_mixedSpace F y.1‖ ≤ r → ∀ x : 𝔸,
      ‖g (ringEquiv_mixedSpace F (x - y).1) * h (x - y).2‖ ≤ bound x := by
  set e := ringEquiv_mixedSpace F with he
  set k : ℕ := decayExp F with hk
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_le F g k
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  set A : ℝ := C * (1 + r) ^ k with hA
  have hA0 : 0 ≤ A := mul_nonneg hC0 (by positivity)
  refine ⟨fun x => A / (1 + ‖e x.1‖) ^ k * ‖h x.2‖, ?_, fun y hy2 hy1 x => ?_⟩
  · obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hlc.continuous
    have hbdd : BddAbove (Set.range fun y => ‖h y‖) := ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩
    refine integrable_of_continuous_of_decay μ _ ?_ hcs (fun x hx => ?_) (A * (⨆ y, ‖h y‖)) (fun x => ?_)
    · have hden : Continuous fun x : 𝔸 => (1 + ‖e x.1‖) ^ k :=
        (continuous_const.add ((AdelicBox.continuous_ringEquiv_mixedSpace F).comp continuous_fst).norm).pow k
      have hden_ne : ∀ x : 𝔸, (1 + ‖e x.1‖) ^ k ≠ 0 := fun x => by positivity
      exact (continuous_const.div hden hden_ne).mul (hlc.continuous.comp continuous_snd).norm
    · refine subset_tsupport _ fun h0 => hx ?_
      simp [h0]
    · have hle : ‖h x.2‖ ≤ ⨆ y, ‖h y‖ := le_ciSup hbdd x.2
      have hpos : 0 < (1 + ‖e x.1‖) ^ k := by positivity
      have hnn : 0 ≤ A / (1 + ‖e x.1‖) ^ k * ‖h x.2‖ := mul_nonneg (div_nonneg hA0 hpos.le) (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc (1 + ‖e x.1‖) ^ k * (A / (1 + ‖e x.1‖) ^ k * ‖h x.2‖) = A * ‖h x.2‖ := by
            field_simp
        _ ≤ A * ⨆ y, ‖h y‖ := mul_le_mul_of_nonneg_left hle hA0
  · have h1 : (x - y).1 = x.1 - y.1 := rfl
    have h2 : (x - y).2 = x.2 := by show x.2 - y.2 = x.2; rw [hy2, sub_zero]
    rw [h1, h2, map_sub]
    set v : E∞ := e y.1 with hv

    have hP : 1 + ‖e x.1‖ ≤ (1 + r) * (1 + ‖e x.1 - v‖) :=
      (one_add_norm_le_mul (e x.1) v).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    have hPk : (1 + ‖e x.1‖) ^ k ≤ (1 + r) ^ k * (1 + ‖e x.1 - v‖) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hP k
    have hg : ‖g (e x.1 - v)‖ ≤ A / (1 + ‖e x.1‖) ^ k := by
      rw [le_div_iff₀ (by positivity), hA]
      calc ‖g (e x.1 - v)‖ * (1 + ‖e x.1‖) ^ k
          ≤ ‖g (e x.1 - v)‖ * ((1 + r) ^ k * (1 + ‖e x.1 - v‖) ^ k) :=
            mul_le_mul_of_nonneg_left hPk (norm_nonneg _)
        _ = (1 + r) ^ k * ((1 + ‖e x.1 - v‖) ^ k * ‖g (e x.1 - v)‖) := by ring
        _ ≤ (1 + r) ^ k * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
        _ = C * (1 + r) ^ k := by ring
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hg (norm_nonneg _)

theorem exists_bound_of_mem_schwartzBruhat [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸)
    [μ.IsAddHaarMeasure] {B : 𝔸 → ℂ} (hB : B ∈ schwartzBruhat F) (r : ℝ) (hr : 0 ≤ r) :
    ∃ bound : 𝔸 → ℝ, Integrable bound μ ∧ ∀ y : 𝔸, y.2 = 0 → ‖ringEquiv_mixedSpace F y.1‖ ≤ r → ∀ x : 𝔸,
      ‖B (x - y)‖ ≤ bound x := by
  induction hB using schwartzBruhat_induction with
  | tensor f hf =>
    obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
    exact exists_bound_pureTensor μ g h hlc hcs r hr
  | zero => exact ⟨0, integrable_zero _ _ _, fun y _ _ x => by simp⟩
  | add f f' _ _ ih ih' =>
    obtain ⟨b₁, hi₁, h₁⟩ := ih
    obtain ⟨b₂, hi₂, h₂⟩ := ih'
    exact ⟨b₁ + b₂, hi₁.add hi₂, fun y hy hy' x =>
      (norm_add_le _ _).trans (add_le_add (h₁ y hy hy' x) (h₂ y hy hy' x))⟩
  | smul c f _ ih =>
    obtain ⟨b, hi, hb⟩ := ih
    refine ⟨fun x => ‖c‖ * b x, hi.const_mul _, fun y hy hy' x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hb y hy hy' x) (norm_nonneg _)

end Ws20.SBDom

end

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (e : mixedEmbedding.mixedSpace F) :
    ∃ bound : AdeleRing (𝓞 F) F → ℝ, Integrable bound μ ∧
      ∀ (x : AdeleRing (𝓞 F) F) (t : ℝ), t ∈ Metric.ball (0 : ℝ) 1 →
        ‖B (x - @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e), 0))‖ ≤ bound x := by
  obtain ⟨bound, hint, hb⟩ :=
    Ws20.SBDom.exists_bound_of_mem_schwartzBruhat (F := F) μ hB ‖e‖ (norm_nonneg e)
  refine ⟨bound, hint, fun x t ht => hb _ rfl ?_ x⟩
  show ‖InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e))‖ ≤ ‖e‖
  rw [RingEquiv.apply_symm_apply, norm_smul, Real.norm_eq_abs]
  have ht' : |t| < 1 := by simpa [Metric.mem_ball, dist_zero_right] using ht
  exact mul_le_of_le_one_left (norm_nonneg _) ht'.le

end S_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le (solution)
