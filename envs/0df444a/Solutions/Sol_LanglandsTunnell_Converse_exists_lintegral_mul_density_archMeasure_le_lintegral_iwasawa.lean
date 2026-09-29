-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/df68448e-7a96-5374-a1b0-6b7f12e2c3c0

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier Topology
open scoped ENNReal NNReal

noncomputable section

namespace Ws23Arch

scoped instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

theorem locallyCompactSpace_GL : LocallyCompactSpace (GL (Fin 2) ℝ) := by infer_instance

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) ℝ) :=
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_rowIsometrySubgroup :
    IsClosed ((rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  have h1 : IsClosed {k : GL (Fin 2) ℝ | ‖(k : Matrix (Fin 2) (Fin 2) ℝ).det‖ = 1} :=
    isClosed_eq (continuous_norm.comp Units.continuous_val.matrix_det) continuous_const
  have h2 : IsClosed {k : GL (Fin 2) ℝ | ∀ x y : ℝ,
      ‖x * (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖ ^ 2 +
        ‖x * (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1‖ ^ 2 =
          ‖x‖ ^ 2 + ‖y‖ ^ 2} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
    have hc : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) ℝ => (k : Matrix (Fin 2) (Fin 2) ℝ) i j :=
      fun i j => Units.continuous_val.matrix_elem i j
    fun_prop
  have : ((rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) =
      {k : GL (Fin 2) ℝ | ‖(k : Matrix (Fin 2) (Fin 2) ℝ).det‖ = 1} ∩ {k : GL (Fin 2) ℝ | ∀ x y : ℝ,
      ‖x * (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖ ^ 2 +
        ‖x * (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1‖ ^ 2 =
          ‖x‖ ^ 2 + ‖y‖ ^ 2} := by
    ext k
    rfl
  rw [this]
  exact h1.inter h2

theorem mem_range_unipotentGL2Hom_iff {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    g ∈ (unipotentGL2Hom (R := R)).range ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) R) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, h00, h10, h11]

theorem isClosed_realUnipotent : IsClosed ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have : ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) =
      ((fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ⁻¹' {0}) ∩
        (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_assoc]
    exact mem_range_unipotentGL2Hom_iff g
  rw [this]
  exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
    (isClosed_singleton.preimage (hc 1 1))

theorem realUnipotent_comm (a b : (realUnipotent : Subgroup (GL (Fin 2) ℝ))) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  apply Subtype.ext
  show (a : GL (Fin 2) ℝ) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem continuous_unipotentGL2 : Continuous (unipotentGL2 : ℝ → GL (Fin 2) ℝ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop
  · have : (fun x : ℝ => ((unipotentGL2 x)⁻¹ : GL (Fin 2) ℝ).val) = fun x => !![1, -x; 0, 1] := rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

def nLine (x : ℝ) : (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨unipotentGL2 x, ⟨Multiplicative.ofAdd x, rfl⟩⟩

@[scoped simp] theorem coe_nLine (x : ℝ) : (nLine x : GL (Fin 2) ℝ) = unipotentGL2 x := rfl

theorem continuous_nLine : Continuous nLine := continuous_unipotentGL2.subtype_mk _

theorem nLine_add (x y : ℝ) : nLine (x + y) = nLine x * nLine y :=
  Subtype.ext (unipotentGL2_add x y)

theorem nLine_surjective : Function.Surjective nLine := by
  rintro ⟨g, ⟨a, rfl⟩⟩
  exact ⟨a.toAdd, rfl⟩

def nCoord (n : (realUnipotent : Subgroup (GL (Fin 2) ℝ))) : ℝ := ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1

theorem continuous_nCoord : Continuous nCoord :=
  (Units.continuous_val.matrix_elem 0 1).comp continuous_subtype_val

theorem nCoord_nLine (x : ℝ) : nCoord (nLine x) = x := by simp [nCoord, nLine, unipotentGL2]

theorem nLine_nCoord (n : (realUnipotent : Subgroup (GL (Fin 2) ℝ))) : nLine (nCoord n) = n := by
  obtain ⟨x, rfl⟩ := nLine_surjective n
  rw [nCoord_nLine]

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (hcomm : ∀ a b : G, a * b = b * a) : μ.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun h : G => h * g) = fun h => g * h := funext fun h => hcomm h g
    rw [this]
    exact map_mul_left_eq_self μ g⟩

theorem measurable_weight {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.ennreal_tsum fun n => ?_
    exact measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet))
  · exact measurable_const

theorem measurable_density {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

theorem coe_upperUnit (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    ((upperUnit a b t ha ht : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coe_upperUnit_inv (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    (((upperUnit a b t ha ht)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a⁻¹, -(b * a⁻¹ * t⁻¹); 0, t⁻¹] := by
  have hmul : (!![a⁻¹, -(b * a⁻¹ * t⁻¹); 0, t⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) * !![a, b; 0, t] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ht]; try (field_simp; ring))
  rw [Matrix.coe_units_inv, coe_upperUnit]
  exact Matrix.inv_eq_left_inv hmul

theorem upperUnit_eq_unipotent_mul {x y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    upperUnit (t * y) (t * x) t (mul_pos ht hy).ne' ht.ne' =
      unipotentGL2 x * upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_upperUnit, coe_upperUnit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def iwB (q : ℝ × ℝ × ℝ) : GL (Fin 2) ℝ :=
  if h : 0 < q.2.1 ∧ 0 < q.2.2 then
    upperUnit (q.2.2 * q.2.1) (q.2.2 * q.1) q.2.2 (mul_pos h.2 h.1).ne' h.2.ne'
  else 1

def iwU : Set (ℝ × ℝ × ℝ) := {q | 0 < q.2.1 ∧ 0 < q.2.2}

theorem isOpen_iwU : IsOpen iwU :=
  (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
    (isOpen_lt continuous_const (continuous_snd.comp continuous_snd))

theorem continuousOn_iwB : ContinuousOn iwB iwU := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : (fun q : iwU => ((iwB (q : ℝ × ℝ × ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun q : iwU => !![q.1.2.2 * q.1.2.1, q.1.2.2 * q.1.1; 0, q.1.2.2] := by
    funext q
    rw [iwB, dif_pos (show 0 < (q : ℝ × ℝ × ℝ).2.1 ∧ 0 < (q : ℝ × ℝ × ℝ).2.2 from q.2), coe_upperUnit]
  have hinv : (fun q : iwU => (((iwB (q : ℝ × ℝ × ℝ))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun q : iwU => !![(q.1.2.2 * q.1.2.1)⁻¹,
        -((q.1.2.2 * q.1.1) * (q.1.2.2 * q.1.2.1)⁻¹ * (q.1.2.2)⁻¹); 0, (q.1.2.2)⁻¹] := by
    funext q
    rw [iwB, dif_pos (show 0 < (q : ℝ × ℝ × ℝ).2.1 ∧ 0 < (q : ℝ × ℝ × ℝ).2.2 from q.2), coe_upperUnit_inv]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun q : iwU => ((iwB (q : ℝ × ℝ × ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hval]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun q : iwU => (((iwB (q : ℝ × ℝ × ℝ))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hinv]
    have h21 : ∀ q : iwU, (q : ℝ × ℝ × ℝ).2.1 ≠ 0 := fun q => q.2.1.ne'
    have h22 : ∀ q : iwU, (q : ℝ × ℝ × ℝ).2.2 ≠ 0 := fun q => q.2.2.ne'
    have c1 : Continuous fun q : iwU => (q : ℝ × ℝ × ℝ).1 := continuous_fst.comp continuous_subtype_val
    have c21 : Continuous fun q : iwU => (q : ℝ × ℝ × ℝ).2.1 :=
      continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
    have c22 : Continuous fun q : iwU => (q : ℝ × ℝ × ℝ).2.2 :=
      continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
    · exact (c21.inv₀ h21).mul (c22.inv₀ h22)
    · exact (((c22.mul c1).mul ((c21.inv₀ h21).mul (c22.inv₀ h22))).mul (c22.inv₀ h22)).neg
    · exact continuous_const
    · exact c22.inv₀ h22

theorem measurable_iwB [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] : Measurable iwB := by
  classical
  have h : iwB = iwU.piecewise iwB (fun _ => 1) := by
    funext q
    by_cases hq : q ∈ iwU
    · rw [Set.piecewise_eq_of_mem _ _ _ hq]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hq, iwB, dif_neg (show ¬ (0 < q.2.1 ∧ 0 < q.2.2) from hq)]
  rw [h]
  exact continuousOn_iwB.measurable_piecewise continuousOn_const isOpen_iwU.measurableSet

section LineIntegral

variable [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]

def lineMeasure : Measure (realUnipotent : Subgroup (GL (Fin 2) ℝ)) := Measure.map nLine volume

theorem measurable_nLine : Measurable nLine := continuous_nLine.measurable

scoped instance lineMeasure_isMulLeftInvariant : (lineMeasure).IsMulLeftInvariant := by
  refine ⟨fun n => ?_⟩
  obtain ⟨a, rfl⟩ := nLine_surjective n
  haveI := secondCountableTopology_GL
  have hm : Measurable fun m : (realUnipotent : Subgroup (GL (Fin 2) ℝ)) => nLine a * m :=
    (continuous_const.mul continuous_id).measurable
  rw [lineMeasure, Measure.map_map hm measurable_nLine]
  have : (fun m : (realUnipotent : Subgroup (GL (Fin 2) ℝ)) => nLine a * m) ∘ nLine = nLine ∘ fun x => a + x := by
    funext x
    simp [Function.comp, nLine_add]
  rw [this, ← Measure.map_map measurable_nLine (measurable_const_add a), map_add_left_eq_self]

scoped instance lineMeasure_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts lineMeasure := by
  refine ⟨fun K hK => ?_⟩
  rw [lineMeasure, Measure.map_apply measurable_nLine hK.measurableSet]
  have : nLine ⁻¹' K = nCoord '' K := by
    ext x
    constructor
    · intro hx
      exact ⟨nLine x, hx, nCoord_nLine x⟩
    · rintro ⟨n, hn, rfl⟩
      show nLine (nCoord n) ∈ K
      rwa [nLine_nCoord]
  rw [this]
  exact (hK.image continuous_nCoord).measure_lt_top

theorem exists_lintegral_density_unipotent_mul [SecondCountableTopology (GL (Fin 2) ℝ)]
    (μN : Measure (realUnipotent : Subgroup (GL (Fin 2) ℝ))) [μN.IsHaarMeasure] :
    ∃ κ : ℝ≥0∞, κ ≠ ⊤ ∧ ∀ g : GL (Fin 2) ℝ,
      ∫⁻ x : ℝ, HaarQuotient.density realUnipotent μN (unipotentGL2 x * g) = κ := by
  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := locallyCompactSpace_GL
  haveI : LocallyCompactSpace (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
    isClosed_realUnipotent.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (realUnipotent : Subgroup (GL (Fin 2) ℝ)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN
  haveI : SFinite μN := instSFiniteOfSigmaFinite
  haveI : μN.IsMulRightInvariant := isMulRightInvariant_of_comm μN realUnipotent_comm
  have hD : Measurable (HaarQuotient.density realUnipotent μN) := measurable_density _ _
  refine ⟨Measure.haarScalarFactor lineMeasure μN, ENNReal.coe_ne_top, fun g => ?_⟩
  have hm : Measurable fun n : (realUnipotent : Subgroup (GL (Fin 2) ℝ)) =>
      HaarQuotient.density realUnipotent μN ((n : GL (Fin 2) ℝ) * g) :=
    hD.comp (continuous_subtype_val.mul continuous_const).measurable
  calc ∫⁻ x : ℝ, HaarQuotient.density realUnipotent μN (unipotentGL2 x * g)
      = ∫⁻ x : ℝ, (fun n : (realUnipotent : Subgroup (GL (Fin 2) ℝ)) =>
          HaarQuotient.density realUnipotent μN ((n : GL (Fin 2) ℝ) * g)) (nLine x) := rfl
    _ = ∫⁻ n : (realUnipotent : Subgroup (GL (Fin 2) ℝ)),
          HaarQuotient.density realUnipotent μN ((n : GL (Fin 2) ℝ) * g) ∂lineMeasure := by
          rw [lineMeasure, lintegral_map hm measurable_nLine]
    _ = ∫⁻ n : (realUnipotent : Subgroup (GL (Fin 2) ℝ)), HaarQuotient.density realUnipotent μN ((n : GL (Fin 2) ℝ) * g)
          ∂(Measure.haarScalarFactor lineMeasure μN • μN) := by
          rw [← Measure.isMulLeftInvariant_eq_smul lineMeasure μN]
    _ = Measure.haarScalarFactor lineMeasure μN := by
          rw [lintegral_smul_measure, HaarQuotient.lintegral_density_mul_eq_one _ isClosed_realUnipotent μN g]
          simp

end LineIntegral

section Main

def iwT (q : (ℝ × ℝ × ℝ) × (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ :=
  iwB q.1 * (q.2 : GL (Fin 2) ℝ)

def iwρ (a : ℝ × ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((a.2.1 ^ 2)⁻¹ * a.2.2⁻¹)

theorem measurable_iwρ : Measurable iwρ := by
  unfold iwρ
  refine ENNReal.measurable_ofReal.comp ?_
  exact ((measurable_fst.comp measurable_snd).pow_const 2).inv.mul (measurable_snd.comp measurable_snd).inv

def quadrant : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioi 0

theorem measurableSet_quadrant : MeasurableSet quadrant := measurableSet_Ioi.prod measurableSet_Ioi

theorem mem_quadrant {r : ℝ × ℝ} : r ∈ quadrant ↔ 0 < r.1 ∧ 0 < r.2 := Set.mem_prod.trans (by simp)

theorem iwB_zero_eq {r : ℝ × ℝ} (h : 0 < r.1 ∧ 0 < r.2) :
    iwB ((0 : ℝ), r) = upperUnit (r.2 * r.1) 0 r.2 (mul_pos h.2 h.1).ne' h.2.ne' := by
  rw [iwB, dif_pos (show 0 < ((0 : ℝ), r).2.1 ∧ 0 < ((0 : ℝ), r).2.2 from h)]
  exact congrArg (fun b => upperUnit (r.2 * r.1) b r.2 (mul_pos h.2 h.1).ne' h.2.ne') (mul_zero _)

theorem iwB_eq_unipotent_mul {x : ℝ} {r : ℝ × ℝ} (h : 0 < r.1 ∧ 0 < r.2) :
    iwB (x, r) = unipotentGL2 x * iwB ((0 : ℝ), r) := by
  rw [iwB_zero_eq h, iwB, dif_pos (show 0 < (x, r).2.1 ∧ 0 < (x, r).2.2 from h)]
  exact upperUnit_eq_unipotent_mul h.1 h.2

theorem unipotentGL2_mem_realUnipotent (x : ℝ) : unipotentGL2 x ∈ (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨Multiplicative.ofAdd x, rfl⟩

theorem main_estimate :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure]
      (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure],
    ∃ C₀ : ENNReal, C₀ ≠ ⊤ ∧
      ∀ (H : GL (Fin 2) ℝ → ENNReal), Measurable H →
        (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, H (n * g) = H g) →
        MeasureTheory.lintegral RSCarrier.archMeasure (fun g => H g * HaarQuotient.density realUnipotent μN g) ≤
          C₀ * MeasureTheory.lintegral ν (fun k : rowIsometrySubgroup ℝ =>
            MeasureTheory.lintegral (volume : Measure (ℝ × ℝ)) (fun q : ℝ × ℝ =>
              if h : 0 < q.1 ∧ 0 < q.2 then
                H (upperUnit (q.2 * q.1) 0 q.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
                  ENNReal.ofReal ((q.1 ^ 2)⁻¹ * q.2⁻¹)
              else 0)) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  intro μN _ ν _
  haveI := secondCountableTopology_GL
  haveI := locallyCompactSpace_GL
  haveI : RSCarrier.archMeasure.IsHaarMeasure :=
    (LanglandsTunnell.Converse.isHaarMeasure_and_isMulRightInvariant_archMeasure).1
  haveI : SecondCountableTopology (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) :=
    isClosed_rowIsometrySubgroup.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite ν := Measure.IsHaarMeasure.sigmaFinite ν
  haveI : SFinite ν := instSFiniteOfSigmaFinite
  haveI : LocallyCompactSpace (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
    isClosed_realUnipotent.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (realUnipotent : Subgroup (GL (Fin 2) ℝ)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN
  haveI : SFinite μN := instSFiniteOfSigmaFinite
  obtain ⟨c, hc, hμ⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa RSCarrier.archMeasure ν
  obtain ⟨κ, hκ, hκg⟩ := exists_lintegral_density_unipotent_mul μN
  refine ⟨(c : ℝ≥0∞) * κ, ENNReal.mul_ne_top ENNReal.coe_ne_top hκ, fun H hH hN => ?_⟩

  set D : GL (Fin 2) ℝ → ℝ≥0∞ := HaarQuotient.density realUnipotent μN with hDdef
  have hDm : Measurable D := measurable_density _ _
  have hT : Measurable iwT :=
    (measurable_iwB.comp measurable_fst).mul (continuous_subtype_val.measurable.comp measurable_snd)
  let L : Measure (ℝ × ℝ × ℝ) :=
    (volume.restrict (Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).withDensity iwρ

  let F : (ℝ × ℝ × ℝ) × (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) → ℝ≥0∞ :=
    fun q => H (iwT q) * D (iwT q)
  have hF : Measurable F := (hH.comp hT).mul (hDm.comp hT)

  have step1 : ∫⁻ g, H g * D g ∂(RSCarrier.archMeasure) ≤ (c : ℝ≥0∞) * ∫⁻ q, F q ∂(L.prod ν) := by
    rw [hμ, lintegral_smul_measure]
    exact mul_le_mul_right (lintegral_map_le _ _) _

  have step2 : ∫⁻ q, F q ∂(L.prod ν) = ∫⁻ a, ∫⁻ k, F (a, k) ∂ν ∂L := lintegral_prod _ hF.aemeasurable
  have hG : Measurable fun a : ℝ × ℝ × ℝ => ∫⁻ k, F (a, k) ∂ν := hF.lintegral_prod_right'

  have step3 : ∫⁻ a, ∫⁻ k, F (a, k) ∂ν ∂L =
      ∫⁻ a in Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), iwρ a * ∫⁻ k, F (a, k) ∂ν ∂volume := by
    show ∫⁻ a, ∫⁻ k, F (a, k) ∂ν ∂((volume.restrict _).withDensity iwρ) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ measurable_iwρ hG]
    rfl

  have step4 : ∫⁻ a in Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), iwρ a * ∫⁻ k, F (a, k) ∂ν ∂volume =
      ∫⁻ r in quadrant, ∫⁻ x : ℝ, iwρ (x, r) * ∫⁻ k, F ((x, r), k) ∂ν ∂volume ∂volume := by
    rw [show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) from rfl,
      show Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) = (Set.univ : Set ℝ) ×ˢ quadrant from rfl,
      ← Measure.prod_restrict, Measure.restrict_univ]
    exact lintegral_prod_symm _ ((measurable_iwρ.mul hG).aemeasurable)

  have step5 : ∀ r ∈ quadrant,
      ∫⁻ x : ℝ, iwρ (x, r) * ∫⁻ k, F ((x, r), k) ∂ν ∂volume =
        ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹) * (κ * ∫⁻ k, H (iwB ((0 : ℝ), r) * (k : GL (Fin 2) ℝ)) ∂ν) := by
    intro r hr
    have h := mem_quadrant.1 hr
    set B : GL (Fin 2) ℝ := iwB ((0 : ℝ), r) with hB
    have hρ : ∀ x : ℝ, iwρ (x, r) = ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹) := fun x => rfl
    have hFx : ∀ (x : ℝ) (k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ))), F ((x, r), k) =
        H (B * (k : GL (Fin 2) ℝ)) * D (unipotentGL2 x * (B * (k : GL (Fin 2) ℝ))) := by
      intro x k
      show H (iwB (x, r) * (k : GL (Fin 2) ℝ)) * D (iwB (x, r) * (k : GL (Fin 2) ℝ)) = _
      rw [iwB_eq_unipotent_mul h, mul_assoc, hN _ (unipotentGL2_mem_realUnipotent x)]
    simp_rw [hρ, hFx]
    have mHk : Measurable fun k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) => H (B * (k : GL (Fin 2) ℝ)) :=
      hH.comp (measurable_const.mul continuous_subtype_val.measurable)
    have mPair : Measurable fun q : ℝ × (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) =>
        H (B * (q.2 : GL (Fin 2) ℝ)) * D (unipotentGL2 q.1 * (B * (q.2 : GL (Fin 2) ℝ))) :=
      (mHk.comp measurable_snd).mul (hDm.comp ((continuous_unipotentGL2.measurable.comp measurable_fst).mul
        (measurable_const.mul (continuous_subtype_val.measurable.comp measurable_snd))))
    have mA : Measurable fun x : ℝ => ∫⁻ k, H (B * (k : GL (Fin 2) ℝ)) *
        D (unipotentGL2 x * (B * (k : GL (Fin 2) ℝ))) ∂ν := mPair.lintegral_prod_right'
    have mB : AEMeasurable (Function.uncurry fun (x : ℝ) (k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ))) =>
        H (B * (k : GL (Fin 2) ℝ)) * D (unipotentGL2 x * (B * (k : GL (Fin 2) ℝ)))) (volume.prod ν) :=
      mPair.aemeasurable
    have mC : ∀ k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)),
        Measurable fun x : ℝ => D (unipotentGL2 x * (B * (k : GL (Fin 2) ℝ))) :=
      fun k => hDm.comp (continuous_unipotentGL2.measurable.mul measurable_const)
    rw [lintegral_const_mul _ mA]
    congr 1
    rw [lintegral_lintegral_swap mB]
    have hin : ∀ k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)),
        ∫⁻ x : ℝ, H (B * (k : GL (Fin 2) ℝ)) * D (unipotentGL2 x * (B * (k : GL (Fin 2) ℝ))) ∂volume =
          H (B * (k : GL (Fin 2) ℝ)) * κ := by
      intro k
      rw [lintegral_const_mul _ (mC k), hκg]
    simp_rw [hin]
    rw [lintegral_mul_const _ mHk, mul_comm]

  have step6 : ∫⁻ r in quadrant, ∫⁻ x : ℝ, iwρ (x, r) * ∫⁻ k, F ((x, r), k) ∂ν ∂volume ∂volume =
      κ * ∫⁻ k, ∫⁻ r : ℝ × ℝ, (if h : 0 < r.1 ∧ 0 < r.2 then
          H (upperUnit (r.2 * r.1) 0 r.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
            ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹) else 0) ∂volume ∂ν := by
    rw [setLIntegral_congr_fun measurableSet_quadrant step5]
    have hm1 : Measurable fun r : ℝ × ℝ => ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹) :=
      ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const 2).inv.mul measurable_snd.inv)
    have hm2 : Measurable fun q : (ℝ × ℝ) × (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) =>
        H (iwB ((0 : ℝ), q.1) * (q.2 : GL (Fin 2) ℝ)) :=
      hH.comp ((measurable_iwB.comp (measurable_const.prodMk measurable_fst)).mul
        (continuous_subtype_val.measurable.comp measurable_snd))
    have hm3 : Measurable fun r : ℝ × ℝ => ∫⁻ k, H (iwB ((0 : ℝ), r) * (k : GL (Fin 2) ℝ)) *
        ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹) ∂ν :=
      (hm2.mul (hm1.comp measurable_fst)).lintegral_prod_right'
    have hm4 : ∀ r : ℝ × ℝ, Measurable fun k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) =>
        H (iwB ((0 : ℝ), r) * (k : GL (Fin 2) ℝ)) :=
      fun r => hH.comp (measurable_const.mul continuous_subtype_val.measurable)
    have hm5 : AEMeasurable (Function.uncurry fun (r : ℝ × ℝ) (k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ))) =>
        H (iwB ((0 : ℝ), r) * (k : GL (Fin 2) ℝ)) * ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹))
        ((volume.restrict quadrant).prod ν) :=
      (hm2.mul (hm1.comp measurable_fst)).aemeasurable
    have e1 : ∀ r : ℝ × ℝ, ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹) *
        (κ * ∫⁻ k, H (iwB ((0 : ℝ), r) * (k : GL (Fin 2) ℝ)) ∂ν) =
        κ * ∫⁻ k, H (iwB ((0 : ℝ), r) * (k : GL (Fin 2) ℝ)) * ENNReal.ofReal ((r.1 ^ 2)⁻¹ * r.2⁻¹) ∂ν := by
      intro r
      rw [lintegral_mul_const _ (hm4 r)]
      ring
    simp_rw [e1]
    rw [lintegral_const_mul _ hm3, lintegral_lintegral_swap hm5]
    congr 1
    refine lintegral_congr fun k => ?_
    rw [← lintegral_indicator measurableSet_quadrant]
    refine lintegral_congr fun r => ?_
    by_cases h : 0 < r.1 ∧ 0 < r.2
    · rw [Set.indicator_of_mem (mem_quadrant.2 h), dif_pos h, iwB_zero_eq h]
    · rw [Set.indicator_of_notMem (fun hr => h (mem_quadrant.1 hr)), dif_neg h]
  calc ∫⁻ g, H g * D g ∂(RSCarrier.archMeasure)
      ≤ (c : ℝ≥0∞) * ∫⁻ q, F q ∂(L.prod ν) := step1
    _ = (c : ℝ≥0∞) * (κ * _) := by rw [step2, step3, step4, step6]
    _ = (c : ℝ≥0∞) * κ * _ := (mul_assoc _ _ _).symm

end Main

end Ws23Arch
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa.Ws23Arch"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa.Ws23Arch"

theorem solution :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure]
      (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure],
    ∃ C₀ : ENNReal, C₀ ≠ ⊤ ∧
      ∀ (H : GL (Fin 2) ℝ → ENNReal), Measurable H →
        (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, H (n * g) = H g) →
        MeasureTheory.lintegral RSCarrier.archMeasure (fun g => H g * HaarQuotient.density realUnipotent μN g) ≤
          C₀ * MeasureTheory.lintegral ν (fun k : rowIsometrySubgroup ℝ =>
            MeasureTheory.lintegral (volume : Measure (ℝ × ℝ)) (fun q : ℝ × ℝ =>
              if h : 0 < q.1 ∧ 0 < q.2 then
                H (upperUnit (q.2 * q.1) 0 q.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
                  ENNReal.ofReal ((q.1 ^ 2)⁻¹ * q.2⁻¹)
              else 0)) := by
  exact Ws23Arch.main_estimate

end S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa (solution)
