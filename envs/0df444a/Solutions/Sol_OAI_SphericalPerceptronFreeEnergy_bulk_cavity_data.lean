-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:16:53.155363+00:00
-- url     : https://prove2.me/submissions/a5e88ad9-a96c-4dc5-a512-f345b31c2952

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_limit_geometry
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_limit_gg
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_marked_self_consistency
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_single_limit_exists
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavity_joint_array_recursion_limit
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedDepthLaw_finiteGG
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedDepthLaw_pair_weights

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_FiniteOverlap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma ultrametric_extension_row {ι L : Type*} [LinearOrder L]
    (A : ι → ι → L) (v : ι → L) (i : ι)
    (hmax : ∀ j, v j ≤ v i)
    (hlo : ∀ j, min (v i) (A i j) ≤ v j)
    (hhi : ∀ j, min (v i) (v j) ≤ A i j) :
    ∀ j, v j = min (v i) (A i j) := by
  intro j
  apply le_antisymm
  · apply le_min (hmax j)
    simpa only [min_eq_right (hmax j)] using hhi j
  · exact hlo j

lemma finite_measure_eq_of_maximal_coordinates
    {ι L : Type*} [Fintype ι] [Nonempty ι] [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (ι → L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set (ι → L)) (hμ : ∀ᵐ v ∂μ, v ∈ S) (hν : ∀ᵐ v ∂ν, v ∈ S)
    (htri : ∀ v ∈ S, ∀ i, (∀ j, v j ≤ v i) → ∀ w ∈ S,
      w i = v i → (∀ j, w j ≤ v i) → w = v)
    (hcoord : ∀ i c, μ.real {v | v i = c} = ν.real {v | v i = c}) : μ = ν := by
  classical
  have hout (v : ι → L) (hv : v ∉ S) : μ.real {v} = 0 ∧ ν.real {v} = 0 := by
    have he (ρ : Measure (ι → L)) (hρ : ∀ᵐ w ∂ρ, w ∈ S) : ρ {v} = 0 :=
      measure_mono_null (by simpa using hv) (ae_iff.mp hρ)
    simp only [measureReal_def,he μ hμ,he ν hν,ENNReal.toReal_zero,and_self]
  have hmass : ∀ v : ι → L, μ.real {v} = ν.real {v} := by
    by_contra h
    have hex : ∃ v : ι → L, μ.real {v} ≠ ν.real {v} := by simpa only [not_forall] using h
    let D : Finset (ι → L) := Finset.univ.filter fun v => μ.real {v} ≠ ν.real {v}
    have hD : D.Nonempty := by obtain ⟨v,hv⟩ := hex; exact ⟨v,by simp [D,hv]⟩
    let M (v : ι → L) : L := (Finset.univ.image v).max' (Finset.univ_nonempty.image v)
    have hbound (v : ι → L) (i : ι) : v i ≤ M v :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    obtain ⟨v,hv,hvmax⟩ := D.exists_max_image M hD
    have hvneq : μ.real {v} ≠ ν.real {v} := (Finset.mem_filter.mp hv).2
    have hvS : v ∈ S := by by_contra hh; exact hvneq (by rw [(hout v hh).1,(hout v hh).2])
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image v) (Finset.univ_nonempty.image v))
    change v i = M v at hi
    have hpivot : ∀ j, v j ≤ v i := fun j => (hbound v j).trans_eq hi.symm
    have hother (w : ι → L) (hwi : w i = v i) (hwv : w ≠ v) : μ.real {w} = ν.real {w} := by
      by_contra hw
      have hwD : w ∈ D := by simp [D,hw]
      have hwS : w ∈ S := by by_contra hh; exact hw (by rw [(hout w hh).1,(hout w hh).2])
      apply hwv
      apply htri v hvS i hpivot w hwS hwi
      intro j
      exact ((hbound w j).trans (hvmax w hwD)).trans_eq hi.symm
    let T : Finset (ι → L) := Finset.univ.filter fun w => w i = v i
    have hvT : v ∈ T := by simp [T]
    have hT : (T : Set (ι → L)) = {w | w i = v i} := by ext w; simp [T]
    have he := hcoord i (v i)
    rw [← hT,← sum_measureReal_singleton,← sum_measureReal_singleton] at he
    rw [← Finset.sum_erase_add _ _ hvT,← Finset.sum_erase_add _ _ hvT] at he
    have hs : (∑ w ∈ T.erase v, μ.real {w}) = ∑ w ∈ T.erase v, ν.real {w} := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hother w (by simpa [T] using (Finset.mem_erase.mp hw).2) (Finset.mem_erase.mp hw).1
    rw [hs] at he
    exact hvneq (add_left_cancel he)
  exact Measure.ext_of_singleton fun v =>
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp (hmass v)

lemma finite_ultrametric_row_law_unique
    {ι L : Type*} [Fintype ι] [Nonempty ι] [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (A : ι → ι → L) (μ ν : Measure (ι → L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ v ∂μ, ∀ i j, min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j)
    (hν : ∀ᵐ v ∂ν, ∀ i j, min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j)
    (hcoord : ∀ i c, μ.real {v | v i = c} = ν.real {v | v i = c}) : μ = ν := by
  apply finite_measure_eq_of_maximal_coordinates μ ν
    {v | ∀ i j, min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j} hμ hν ?_ hcoord
  intro v hv i hmax w hw hwi hwmax
  have hvrow := ultrametric_extension_row A v i hmax
    (fun j => (hv i j).1) (fun j => (hv i j).2)
  have hwrow := ultrametric_extension_row A w i (by simpa only [hwi] using hwmax)
    (fun j => (hw i j).1) (fun j => (hw i j).2)
  funext j
  rw [hwrow j,hvrow j,hwi]

lemma finiteBlock_measurable {L : Type*} [MeasurableSpace L] (n : ℕ) :
    Measurable (finiteBlock (L := L) n) :=
  Measurable.of_eval fun row => Measurable.of_eval fun column =>
    (measurable_pi_apply (column : ℕ)).comp (measurable_pi_apply (row : ℕ))

lemma finiteRow_measurable {L : Type*} [MeasurableSpace L] (n : ℕ) :
    Measurable (finiteRow (L := L) n) :=
  Measurable.of_eval fun row =>
    (measurable_pi_apply n).comp (measurable_pi_apply (row : ℕ))

lemma finiteFiberRow_real {L : Type*} [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] (μ : Measure (FiniteOverlap L))
    (n : ℕ) (A : FiniteBlock L n) (i : Fin n) (c : L) :
    (finiteFiberRow μ n A).real {v | v i = c} =
      μ.real {R | finiteBlock n R = A ∧ R i n = c} := by
  rw [measureReal_def,finiteFiberRow,Measure.map_apply (finiteRow_measurable n)
    (show MeasurableSet {v : Fin n → L | v i = c} from (Set.to_countable _).measurableSet),
    Measure.restrict_apply ((finiteRow_measurable n) ((Set.to_countable _).measurableSet))]
  congr 1
  congr 1
  ext R
  simp [finiteRow,and_comm]

lemma finiteFiberRow_unique {L : Type*} [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (FiniteOverlap L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ R ∂μ, (∀ i j, R i j = R j i) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hGGμ : FiniteGG μ) (hGGν : FiniteGG ν)
    (hpair : ∀ c, μ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c})
    (n : ℕ) (hn : 1 ≤ n)
    (hblock : μ.map (finiteBlock n) = ν.map (finiteBlock n))
    (A : FiniteBlock L n) : finiteFiberRow μ n A = finiteFiberRow ν n A := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he : MeasurableSet {R : FiniteOverlap L | finiteBlock n R = A} :=
    (finiteBlock_measurable n) (measurableSet_singleton A)
  have hbase : μ.real {R | finiteBlock n R = A} = ν.real {R | finiteBlock n R = A} := by
    have hh := congrArg (fun ρ : Measure (FiniteBlock L n) => ρ.real {A}) hblock
    simpa only [measureReal_def,Measure.map_apply (finiteBlock_measurable n)
      (measurableSet_singleton A),Set.preimage,Set.mem_singleton_iff] using hh
  have hprev (i j : Fin n) (c : L) :
      μ.real {R | finiteBlock n R = A ∧ R i j = c} =
      ν.real {R | finiteBlock n R = A ∧ R i j = c} := by
    have hset : {R : FiniteOverlap L | finiteBlock n R = A ∧ R i j = c} =
        if A i j = c then {R | finiteBlock n R = A} else ∅ := by
      ext R
      by_cases hA : A i j = c
      · simp only [hA,ite_true,mem_ofPred_eq,and_iff_left_iff_imp]
        intro hR
        exact (congrFun (congrFun hR i) j).trans hA
      · simp only [hA,ite_false,mem_empty_iff_false,mem_ofPred_eq,iff_false,not_and]
        intro hR hh
        exact hA ((congrFun (congrFun hR i) j).symm.trans hh)
    rw [hset]
    split_ifs
    · exact hbase
    · simp
  have hrow (ρ : Measure (FiniteOverlap L))
      (hρ : ∀ᵐ R ∂ρ, (∀ i j, R i j = R j i) ∧
        ∀ i j k, min (R i j) (R i k) ≤ R j k) :
      ∀ᵐ v ∂finiteFiberRow ρ n A, ∀ i j,
        min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j := by
    rw [finiteFiberRow,ae_map_iff (finiteRow_measurable n).aemeasurable (Set.to_countable _).measurableSet]
    apply (ae_restrict_iff' he).mpr
    filter_upwards [hρ] with R hR hRA
    intro i j
    have hij : R i j = A i j := congrFun (congrFun hRA i) j
    dsimp [finiteRow]
    constructor
    · simpa only [← hij,hR.1 n (j : ℕ)] using hR.2 (i : ℕ) n (j : ℕ)
    · simpa only [hR.1 n (i : ℕ),hR.1 n (j : ℕ),hij] using hR.2 n (i : ℕ) (j : ℕ)
  let : IsFiniteMeasure (μ.restrict {R | finiteBlock n R = A}) := inferInstance
  let : IsFiniteMeasure (ν.restrict {R | finiteBlock n R = A}) := inferInstance
  have : IsFiniteMeasure (finiteFiberRow μ n A) := by unfold finiteFiberRow; infer_instance
  have : IsFiniteMeasure (finiteFiberRow ν n A) := by unfold finiteFiberRow; infer_instance
  apply finite_ultrametric_row_law_unique A _ _ (hrow μ hμ) (hrow ν hν)
  intro i c
  rw [finiteFiberRow_real,finiteFiberRow_real,hGGμ n hn i A c,hGGν n hn i A c,hbase,hpair]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact hprev i j c

lemma map_pair_eq_of_fiber_map_eq
    {Ω X Y : Type*} [MeasurableSpace Ω] [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ ν : Measure Ω) (a : Ω → X) (v : Ω → Y)
    (ha : Measurable a) (hv : Measurable v)
    (h : ∀ x, (μ.restrict {ω | a ω = x}).map v =
      (ν.restrict {ω | a ω = x}).map v) :
    μ.map (fun ω => (a ω,v ω)) = ν.map (fun ω => (a ω,v ω)) := by
  apply Measure.ext_of_singleton
  intro p
  have hh := congrArg (fun ρ : Measure Y => ρ {p.2}) (h p.1)
  rw [Measure.map_apply hv (measurableSet_singleton _),
    Measure.map_apply hv (measurableSet_singleton _),
    Measure.restrict_apply (hv (measurableSet_singleton _)),
    Measure.restrict_apply (hv (measurableSet_singleton _))] at hh
  rw [Measure.map_apply (ha.prodMk hv) (measurableSet_singleton _),
    Measure.map_apply (ha.prodMk hv) (measurableSet_singleton _)]
  convert hh using 1 <;> congr 1 <;> ext ω <;> simp [and_comm,Prod.ext_iff]

lemma finiteBlock_eq_extension {L : Type*} (d : L) (R : FiniteOverlap L)
    (hsym : ∀ i j, R i j = R j i) (hdiag : ∀ i, R i i = d) (n : ℕ) :
    finiteBlock (n+1) R = finiteExtension d (finiteBlock n R,finiteRow n R) := by
  funext i j
  refine Fin.lastCases ?_ (fun ii => ?_) i
  · refine Fin.lastCases ?_ (fun jj => ?_) j
    · simpa [finiteBlock,finiteExtension] using hdiag n
    · simpa [finiteBlock,finiteRow,finiteExtension] using hsym n jj
  · refine Fin.lastCases ?_ (fun jj => ?_) j
    · simp [finiteBlock,finiteRow,finiteExtension]
    · simp [finiteBlock,finiteExtension]

lemma finiteBlock_succ_law_unique {L : Type*} [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (FiniteOverlap L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (d : L)
    (hμ : ∀ᵐ R ∂μ, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hGGμ : FiniteGG μ) (hGGν : FiniteGG ν)
    (hpair : ∀ c, μ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c})
    (n : ℕ) (hn : 1 ≤ n)
    (hblock : μ.map (finiteBlock n) = ν.map (finiteBlock n)) :
    μ.map (finiteBlock (n+1)) = ν.map (finiteBlock (n+1)) := by
  have hjoint : μ.map (fun R => (finiteBlock n R,finiteRow n R)) =
      ν.map (fun R => (finiteBlock n R,finiteRow n R)) :=
    map_pair_eq_of_fiber_map_eq μ ν _ _ (finiteBlock_measurable n) (finiteRow_measurable n)
      fun A => finiteFiberRow_unique μ ν
        (hμ.mono fun _ h => ⟨h.1,h.2.2⟩) (hν.mono fun _ h => ⟨h.1,h.2.2⟩)
        hGGμ hGGν hpair n hn hblock A
  have hext (ρ : Measure (FiniteOverlap L))
      (hρ : ∀ᵐ R ∂ρ, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
        ∀ i j k, min (R i j) (R i k) ≤ R j k) :
      ρ.map (finiteBlock (n+1)) =
        (ρ.map (fun R => (finiteBlock n R,finiteRow n R))).map (finiteExtension d) := by
    rw [Measure.map_map (measurable_of_countable _)
      ((finiteBlock_measurable n).prodMk (finiteRow_measurable n))]
    apply Measure.map_congr
    exact hρ.mono fun R hR => finiteBlock_eq_extension d R hR.1 hR.2.1 n
  rw [hext μ hμ,hext ν hν,hjoint]

theorem finiteGG_block_law_unique {L : Type*} [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (FiniteOverlap L)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d : L)
    (hμ : ∀ᵐ R ∂μ, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hGGμ : FiniteGG μ) (hGGν : FiniteGG ν)
    (hpair : ∀ c, μ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c}) :
    ∀ n, μ.map (finiteBlock (n+1)) = ν.map (finiteBlock (n+1)) := by
  have hbase (ρ : Measure (FiniteOverlap L)) [IsProbabilityMeasure ρ]
      (hρ : ∀ᵐ R ∂ρ, ∀ i, R i i = d) :
      ρ.map (finiteBlock 1) = Measure.dirac (fun (_ _ : Fin 1) => d) := by
    have he : finiteBlock 1 =ᵐ[ρ] (fun _ => fun (_ _ : Fin 1) => d) := by
      filter_upwards [hρ] with R hR
      funext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      simpa [hi,hj,finiteBlock] using hR 0
    rw [Measure.map_congr he]
    simp
  intro n
  induction n with
  | zero =>
      exact (hbase μ (hμ.mono fun _ h => h.2.1)).trans
        (hbase ν (hν.mono fun _ h => h.2.1)).symm
  | succ n ih =>
      exact finiteBlock_succ_law_unique μ ν d hμ hν hGGμ hGGν hpair
        (n+1) (by omega) ih

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLogIntensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma standardGaussian_density_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert! hd using 1
  · funext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,Pi.neg_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat]
    norm_num
    ring

lemma standardGaussian_density_mul_integrable :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [show -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma standardGaussian_integrationByParts {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hm : Measurable F')
    {C D : ℝ} (hb : ∀ x, |F x| ≤ C) (hb' : ∀ x, |F' x| ≤ D) :
    ∫ x, x * F x ∂gaussianReal 0 1 = ∫ x, F' x ∂gaussianReal 0 1 := by
  have hfm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have h1 : Integrable (fun x => gaussianPDFReal 0 1 x * F' x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb' x)
  have h2 : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) * F x) := by
    have hh := standardGaussian_density_mul_integrable.neg.mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
    simpa only [neg_mul,Pi.neg_apply] using hh
  have h3 : Integrable (fun x => gaussianPDFReal 0 1 x * F x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => standardGaussian_density_deriv x) (fun x _ => hF x) h1 h2 h3
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul]
  rw [he]
  simp only [neg_mul,integral_neg,neg_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_integrable {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    Integrable (fun x => Real.exp (t * v x) * F x) μ := by
  refine Integrable.of_bound (hv.const_mul t |>.exp.mul hF).aestronglyMeasurable
    (Real.exp (|t| * C) * D) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hFD x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * v x)).trans (by rw [abs_mul]; gcongr; exact hvC x)

lemma tilt_partition_pos {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    0 < tiltPartition μ v t := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC (by norm_num : (0:ℝ) ≤ 1)
      hvC (fun _ => by norm_num) t
  have he : Real.exp (- |t| * C) ≤ tiltPartition μ v t := by
    calc
      Real.exp (- |t| * C) = ∫ _ : S, Real.exp (- |t| * C) ∂μ := by simp
      _ ≤ tiltPartition μ v t := integral_mono_ae (integrable_const _) hi (ae_of_all _ fun x => by
        apply Real.exp_le_exp.mpr
        have hh : |t*v x| ≤ |t| * C := by rw [abs_mul]; gcongr; exact hvC x
        nlinarith [neg_abs_le (t*v x)])
  exact (Real.exp_pos _).trans_le he

lemma tilt_mean_bound {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    |tiltMean μ v F t| ≤ D := by
  have hp := tilt_partition_pos μ hv hC hvC t
  have hi := tilt_integrable μ hv hF hC hD hvC hFD t
  have hiExp : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  rw [tiltMean,abs_div,abs_of_pos hp,div_le_iff₀ hp]
  calc
    |tiltIntegral μ v F t| ≤ ∫ x, |Real.exp (t * v x) * F x| ∂μ := by
      simpa only [tiltIntegral,Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => Real.exp (t * v x) * F x)
    _ ≤ ∫ x, Real.exp (t * v x) * D ∂μ := by
      apply integral_mono_ae hi.norm (hiExp.mul_const D)
      exact ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs]
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hFD x) (Real.exp_pos _).le
    _ = D * tiltPartition μ v t := by rw [integral_mul_const]; exact mul_comm _ _

lemma tilt_law_probability {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    IsProbabilityMeasure (tiltLaw μ v t) := by
  have hp := tilt_partition_pos μ hv hC hvC t
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  constructor
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ .univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

lemma tilt_law_integral {v F : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    ∫ x, F x ∂tiltLaw μ v t = tiltMean μ v F t := by
  rw [tiltLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (Real.exp (t * v x))) from (hv.const_mul t).exp.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (tilt_partition_pos μ hv hC hvC t).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltMean,tiltIntegral]
  exact (div_eq_inv_mul _ _).symm

end Tilt

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

lemma replicaPotential_bound {S : Type*} {v : S → ℝ} {C : ℝ}
    (hv : ∀ x, |v x| ≤ C) (n : ℕ) (x : Fin n → S) :
    |replicaPotential v n x| ≤ n*C := by
  calc
    |∑ i, v (x i)| ≤ ∑ i, |v (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, C := Finset.sum_le_sum (fun i _ => hv (x i))
    _ = n*C := by simp

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_partition {v : S → ℝ} (_hv : Measurable v) (n : ℕ) (t : ℝ) :
    tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      (tiltPartition μ v t)^n := by
  unfold tiltPartition replicaPotential
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x))]
  simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

section GibbsProducts
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_law_apply {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ v t s = (ENNReal.ofReal (tiltPartition μ v t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * v x) ∂μ) := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  have := tilt_law_probability μ hv hC hvC t
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply _ (replicaPotential_measurable hv n)
    (mul_nonneg (Nat.cast_nonneg n) hC) (replicaPotential_bound hvC n) t (MeasurableSet.univ_pi hs),
    replica_partition μ hv n,ENNReal.ofReal_pow (tilt_partition_pos μ hv hC hvC t).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential v n x) =
      ∏ i, Real.exp (t * v (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply μ hv hC hvC t (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

end GibbsProducts

lemma gaussian_pi_coordinate_integrationByParts (n : ℕ) (i : Fin (n+1))
    {F D : (Fin (n+1) → ℝ) → ℝ} (hF : Measurable F) (hD : Measurable D)
    {C B : ℝ} (hFC : ∀ g, |F g| ≤ C) (hDB : ∀ g, |D g| ≤ B)
    (hd : ∀ (g : Fin n → ℝ) (t : ℝ),
      HasDerivAt (fun u => F (i.insertNth u g)) (D (i.insertNth t g)) t) :
    (∫ g, g i * F g ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, D g ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hmF : Measurable (fun p : ℝ × (Fin n → ℝ) => F (i.insertNth p.1 p.2)) :=
    hF.comp e.measurable
  have hmD : Measurable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2)) :=
    hD.comp e.measurable
  have hiF : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1 * F (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) := by
    apply ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).comp_fst ν |>.mul_bdd
      hmF.aestronglyMeasurable
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hFC (i.insertNth p.1 p.2)
  have hiD : Integrable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) :=
    Integrable.of_bound hmD.aestronglyMeasurable B
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hDB (i.insertNth p.1 p.2))
  rw [← he.integral_comp e.measurableEmbedding (fun g => g i * F g),
    ← he.integral_comp e.measurableEmbedding D]
  change (∫ p : ℝ × (Fin n → ℝ), ((i.insertNth p.1 p.2 : Fin (n+1) → ℝ) i) *
    F (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν) =
      ∫ p : ℝ × (Fin n → ℝ), D (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν
  simp only [Fin.insertNth_apply_same]
  rw [integral_prod_symm _ hiF,integral_prod_symm _ hiD]
  apply integral_congr_ae
  exact ae_of_all _ fun g => standardGaussian_integrationByParts (hd g)
    (hmD.comp (measurable_id.prodMk measurable_const))
    (fun t => hFC (i.insertNth t g)) (fun t => hDB (i.insertNth t g))

section GaussianField
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma gaussianField_measurable {n : ℕ} {v : Fin n → S → ℝ}
    (hv : ∀ i, Measurable (v i)) :
    Measurable (fun p : (Fin n → ℝ) × S => gaussianField n v p.1 p.2) := by
  unfold gaussianField
  fun_prop

omit [MeasurableSpace S] in
lemma gaussianField_insertNth {n : ℕ} (i : Fin (n+1)) (v : Fin (n+1) → S → ℝ)
    (g : Fin n → ℝ) (t : ℝ) (x : S) :
    gaussianField (n+1) v (i.insertNth t g) x =
      t*v i x + gaussianField n (fun j => v (i.succAbove j)) g x := by
  classical
  rw [gaussianField,Fin.sum_univ_succAbove _ i]
  simp [gaussianField]

omit [IsProbabilityMeasure μ] in
lemma tilt_mean_mulObservable {v F : S → ℝ} (c t : ℝ) :
    tiltMean μ v (fun x => c*F x) t = c * tiltMean μ v F t := by
  unfold tiltMean tiltIntegral
  simp_rw [show ∀ x, Real.exp (t*v x)*(c*F x) = c*(Real.exp (t*v x)*F x) by intro; ring]
  rw [integral_const_mul]
  ring

end GaussianField

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_replica_integral {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ)
    (F : (Fin n → S) → ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t =
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  rw [← tilt_law_pi μ hv hC hvC n t,tilt_law_integral _
    (replicaPotential_measurable hv n) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n)]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma realTail_lower (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    1 - B ≤ realTail μ x := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (realTail_integrable μ x) (by
      filter_upwards [hμ] with s hs
      exact sub_le_sub_left (max_le hx hs) 1)

lemma cappedDensity_eq (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    cappedDensity μ B x = (realTail μ x)⁻¹ ^ 2 := by
  rw [cappedDensity, max_eq_right (realTail_lower μ hμ hx)]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedCDF
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma cappedA_eq_integral (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    cappedA μ B r = ∫ t in 0..r, (realTail μ t)⁻¹ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hr] at hx
  exact cappedDensity_eq μ hμ (hx.2.trans hrB)

lemma boundedCDF_nonneg (μ : Measure Time) (r : Time) : 0 ≤ boundedCDF μ r :=
  measureReal_nonneg

lemma boundedCDF_le_one (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    boundedCDF μ r ≤ 1 := by
  rw [boundedCDF_eq]
  exact cdf_le_one _ _

theorem boundedQuantile_law (μ : Measure Time) [IsProbabilityMeasure μ] :
    (volume : Measure Time).map (boundedQuantile μ) = μ := by
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply (boundedQuantile_measurable μ) measurableSet_Iic]
  have hpre : boundedQuantile μ ⁻¹' Iic r =
      Iic (⟨boundedCDF μ r, boundedCDF_nonneg μ r, boundedCDF_le_one μ r⟩ : Time) := by
    ext u
    exact boundedQuantile_le_iff μ u r
  rw [hpre, unitInterval.volume_Iic]
  exact ENNReal.ofReal_toReal (measure_ne_top μ _)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegrableGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_of_integrable {H F : S → ℝ} (hH : Measurable H) (_hF : Measurable F)
    {t C : ℝ} (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    (hC : ∀ x, |F x| ≤ C) : |tiltMean μ H F t| ≤ C := by
  let := tilt_law_probability_of_integrable μ hi
  rw [← tilt_law_integral_of_integrable μ hH hi]
  have hh := norm_integral_le_of_norm_le_const (μ := tiltLaw μ H t) (f := F)
    (C := C) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TiltReplicaCoordinate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
section ReplicaCalculus
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_replica_coordinate {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (j : Fin n) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (fun x => F (x j)) t =
      tiltMean μ v F t := by
  have := tilt_law_probability μ hv hC hvC t
  rw [tilt_replica_integral μ hv hC hvC,← tilt_law_integral μ hv hC hvC t]
  have he := measurePreserving_eval (fun _ : Fin n => tiltLaw μ v t) j
  conv_rhs => rw [← he.map_eq,integral_map he.measurable.aemeasurable hF.aestronglyMeasurable]

lemma tilt_mean_sum {ι : Type*} (s : Finset ι) {v : S → ℝ} {F : ι → S → ℝ}
    (hv : Measurable v) (hF : ∀ i ∈ s, Measurable (F i))
    {C : ℝ} {D : ι → ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C)
    (hFD : ∀ i ∈ s, ∀ x, |F i x| ≤ D i) (t : ℝ) :
    tiltMean μ v (fun x => ∑ i ∈ s, F i x) t = ∑ i ∈ s, tiltMean μ v (F i) t := by
  have := tilt_law_probability μ hv hC hvC t
  simp_rw [← tilt_law_integral μ hv hC hvC t]
  exact integral_finsetSum s fun i hi => Integrable.of_bound (hF i hi).aestronglyMeasurable
    (D i) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFD i hi x)

lemma tilt_replica_sum {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D)
    (n : ℕ) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (replicaPotential F n) t =
      n * tiltMean μ v F t := by
  change tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n)
    (fun x => ∑ i, F (x i)) t = _
  rw [tilt_mean_sum (Measure.pi fun _ : Fin n => μ) Finset.univ
    (F := fun i (x : Fin n → S) => F (x i)) (replicaPotential_measurable hv n)
    (fun i _ => hF.comp (measurable_pi_apply i)) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n) (fun i _ x => hFD (x i))]
  simp_rw [tilt_replica_coordinate μ hv hF hC hvC]
  simp

lemma tilt_replica_new_product {n : ℕ} {v F : S → ℝ} {G : (Fin n → S) → ℝ}
    (hv : Measurable v) (hF : Measurable F) (hG : Measurable G)
    {C D B : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C)
    (hFD : ∀ x, |F x| ≤ D) (hGB : ∀ x, |G x| ≤ B) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin (n+1) => μ) (replicaPotential v (n+1))
      (fun x => F (x 0) * G (fun j => x j.succ)) t =
      tiltMean μ v F t * tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) G t := by
  have := tilt_law_probability μ hv hC hvC t
  simp_rw [tilt_replica_integral μ hv hC hvC]
  rw [← tilt_law_integral μ hv hC hvC t]
  let ν := tiltLaw μ v t
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm
  rw [← he.integral_comp' (fun x => F (x 0) * G (fun j => x j.succ))]
  change (∫ p : S × (Fin n → S), F ((Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) 0) *
    G (fun j => (Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) j.succ)
      ∂ν.prod (Measure.pi fun _ => ν)) = _
  simp only [Fin.insertNth_zero',Fin.cons_zero,Fin.cons_succ]
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable D
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFD x)
  have hGi : Integrable G (Measure.pi fun _ : Fin n => ν) := Integrable.of_bound
    hG.aestronglyMeasurable B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGB x)
  rw [integral_prod _ (hFi.mul_prod hGi)]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

end ReplicaCalculus

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
lemma gaussianRows_apply (v : ι → E) (x : E) (i : ι) :
    gaussianRows v x i = inner ℝ (v i) x := rfl

end GaussianRows

open TopologicalSpace

lemma weak_limit_closed_full {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [HasOuterApproxClosed K]
    {μ : ℕ → ProbabilityMeasure K} {ν : ProbabilityMeasure K}
    (hμ : Tendsto μ atTop (𝓝 ν)) {F : Set K} (hF : IsClosed F)
    (hfull : ∀ n, μ n F = 1) : ν F = 1 := by
  apply le_antisymm (ProbabilityMeasure.apply_le_one _ _)
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hF
  have hf (n : ℕ) : (μ n : Measure K) F = 1 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hfull n,ENNReal.coe_one]
  simp only [hf,limsup_const] at h
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact_mod_cast h

lemma compactGG_joint_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) {n : ℕ} (hn : 0 < n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ), compactGGDefect μ n i f g = 0) :
    (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i n)) =
      ((n : ℝ≥0)⁻¹) •
        (((μ : Measure (CompactArray K)).map (compactBlock n)).prod
            ((μ : Measure (CompactArray K)).map (fun Q => Q 0 1)) +
          ∑ j ∈ Finset.univ.erase i,
            (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i j))) := by
  classical
  have hb := (compactBlock_continuous (K := K) n).measurable
  have he (k l : ℕ) : Measurable (fun Q : CompactArray K => Q k l) := by fun_prop
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  let F : (CompactBlock K n × K) →ᵇ ℝ :=
    (f.compContinuous ⟨Prod.fst,continuous_fst⟩) * (g.compContinuous ⟨Prod.snd,continuous_snd⟩)
  have hF : ∀ ρ : Measure (CompactBlock K n × K), IsFiniteMeasure ρ → Integrable F ρ := by
    intro ρ hρ
    exact F.integrable ρ
  change ∫ p, F p ∂_ = ∫ p, F p ∂_
  rw [integral_smul_nnreal_measure,integral_add_measure (hF _ inferInstance) (hF _ inferInstance),
    integral_finsetSum_measure]
  · simp_rw [integral_map (hb.prodMk (he _ _)).aemeasurable F.continuous.aestronglyMeasurable]
    simp only [F,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk,NNReal.smul_def,NNReal.coe_inv,NNReal.coe_natCast,smul_eq_mul]
    rw [integral_prod_mul,integral_map hb.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map (he 0 1).aemeasurable g.continuous.aestronglyMeasurable]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h := hGG f g
    unfold compactGGDefect at h
    apply (mul_right_inj' hn').mp
    rw [←mul_assoc,mul_inv_cancel₀ hn',one_mul]
    linarith [h]
  · intro j hj
    exact hF _ inferInstance

open scoped Polynomial

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedAncestry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma indexedCommonDepth_comm (n : ℕ) (l m : IndexedLeaf n) :
    indexedCommonDepth n l m = indexedCommonDepth n m l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indexedCommonDepth,ih m.2.2 l.2.2,eq_comm]

lemma indexedCommonDepth_self (n : ℕ) (l : IndexedLeaf n) :
    indexedCommonDepth n l l = Fin.last n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [indexedCommonDepth,ih]

lemma indexedLeafVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin n) :
    indexedLeafVertex n l i=indexedLeafVertex n m i ↔ i.val< (indexedCommonDepth n l m).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    by_cases he : l.1=m.1 ∧ l.2.1=m.2.1
    · rcases he with ⟨h1,h2⟩
      rw [indexedCommonDepth,ite_eq_left ⟨h1,h2⟩]
      induction i using Fin.cases with
      | zero => simp [indexedLeafVertex,h1,h2]
      | succ i =>
        simpa [indexedLeafVertex,h1,h2] using ih l.2.2 m.2.2 i
    · rw [indexedCommonDepth,ite_eq_right he]
      induction i using Fin.cases <;> simp_all [indexedLeafVertex,Prod.mk.injEq]

lemma indexedLeafSharedVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m i ↔ i ≤ indexedCommonDepth n l m := by
  induction i using Fin.cases with
  | zero => simp [indexedLeafSharedVertex]
  | succ i =>
    simpa only [indexedLeafSharedVertex,Fin.cases_succ,Sum.inr.injEq,
      Fin.le_iff_val_le_val,Fin.val_succ,Nat.succ_le_iff] using indexedLeafVertex_eq_iff n l m i

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_GibbsReplicaMean
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replicaMean_bound {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable H) (hG : Measurable G) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hHA : ∀ x, |H x| ≤ A) (hGD : ∀ x, |G x| ≤ D) : |gibbsReplicaMean μ H n G| ≤ D :=
  tilt_mean_bound _ (replicaPotential_measurable hH n) hG
    (mul_nonneg (Nat.cast_nonneg n) hA) hD (replicaPotential_bound hHA n) hGD 1

lemma replicaMean_sum {ι : Type*} (t : Finset ι) {H : S → ℝ} {n : ℕ}
    {G : ι → (Fin n → S) → ℝ} (hH : Measurable H)
    (hG : ∀ i ∈ t, Measurable (G i)) {A : ℝ} {D : ι → ℝ}
    (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A)
    (hGD : ∀ i ∈ t, ∀ x, |G i x| ≤ D i) :
    gibbsReplicaMean μ H n (fun x => ∑ i ∈ t, G i x) = ∑ i ∈ t, gibbsReplicaMean μ H n (G i) :=
  tilt_mean_sum _ t (replicaPotential_measurable hH n) hG
    (mul_nonneg (Nat.cast_nonneg n) hA) (replicaPotential_bound hHA n) hGD 1

omit [IsProbabilityMeasure μ] in
lemma replicaMean_const_mul {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ} (c : ℝ) :
    gibbsReplicaMean μ H n (fun x => c*G x) = c*gibbsReplicaMean μ H n G :=
  tilt_mean_mulObservable _ c 1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_VarianceProdMemLp
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma measurable_tiltMean_param {Ω : Type*} [MeasurableSpace Ω] {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (fun ω => tiltMean μ (H ω) (Y ω) 1) := by
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
  exact ((hH.exp.mul hY).stronglyMeasurable.integral_prod_right'.measurable).div
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_replicaMean_param {Ω : Type*} [MeasurableSpace Ω]
    {H : Ω → S → ℝ} {n : ℕ} {Y : Ω → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (fun ω => gibbsReplicaMean μ (H ω) n (Y ω)) := by
  apply measurable_tiltMean_param _ _ hY
  change Measurable (fun p : Ω×(Fin n → S) => ∑ i, H p.1 (p.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_IntegrableReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_general {H F : S → ℝ} (hH : Measurable H) (hF : Measurable F)
    {t C : ℝ} (hC : 0 ≤ C) (hFC : ∀ x, |F x| ≤ C) :
    |tiltMean μ H F t| ≤ C := by
  by_cases hi : Integrable (fun x => Real.exp (t*H x)) μ
  · exact tiltMean_bound_of_integrable μ hH hF hi hFC
  · simp only [tiltMean,tiltPartition,integral_undef hi,div_zero,abs_zero]
    exact hC

lemma replica_exp_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    Integrable (fun x : Fin n → S => Real.exp (t*replicaPotential H n x))
      (Measure.pi fun _ : Fin n => μ) := by
  simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  exact Integrable.fintype_prod (fun _ => hi)

omit [IsProbabilityMeasure μ] in
lemma tilt_law_apply_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ H t s = (ENNReal.ofReal (tiltPartition μ H t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * H x) ∂μ) := by
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi_of_integrable {H : S → ℝ} (hH : Measurable H) {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential H n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ H t) := by
  let := tilt_law_probability_of_integrable μ hi
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply_of_integrable _ (replica_exp_integrable μ hi n) (MeasurableSet.univ_pi hs),
    replica_partition μ hH n,ENNReal.ofReal_pow (tilt_partition_pos_of_integrable μ hi).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential H n x) =
      ∏ i, Real.exp (t * H (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * H x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply_of_integrable μ hi (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

lemma gibbsReplicaMean_integral_of_integrable {H : S → ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (n : ℕ) (G : (Fin n → S) → ℝ) :
    gibbsReplicaMean μ H n G = ∫ x, G x ∂Measure.pi (fun _ : Fin n => tiltLaw μ H 1) := by
  rw [← tilt_law_pi_of_integrable μ hH (by simpa only [one_mul] using hi),
    tilt_law_integral_of_integrable _ (replicaPotential_measurable hH n)
      (replica_exp_integrable μ (by simpa only [one_mul] using hi) n)]
  rfl

lemma gibbsReplicaMean_bound_of_integrable {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable H) (hG : Measurable G) {D : ℝ}
    (hi : Integrable (fun x => Real.exp (H x)) μ) (hGD : ∀ x, |G x| ≤ D) :
    |gibbsReplicaMean μ H n G| ≤ D :=
  tiltMean_bound_of_integrable _ (replicaPotential_measurable hH n) hG
    (replica_exp_integrable μ (by simpa only [one_mul] using hi) n) hGD

lemma gibbsReplicaMean_sum_of_integrable {ι : Type*} (s : Finset ι)
    {H : S → ℝ} {n : ℕ} {G : ι → (Fin n → S) → ℝ}
    (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (hG : ∀ i ∈ s, Measurable (G i)) {D : ι → ℝ}
    (hGD : ∀ i ∈ s, ∀ x, |G i x| ≤ D i) :
    gibbsReplicaMean μ H n (fun x => ∑ i ∈ s, G i x) =
      ∑ i ∈ s, gibbsReplicaMean μ H n (G i) := by
  let := tilt_law_probability_of_integrable μ (by simpa only [one_mul] using hi :
    Integrable (fun x => Real.exp (1*H x)) μ)
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  exact integral_finsetSum s fun i hi => Integrable.of_bound (hG i hi).aestronglyMeasurable
    (D i) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGD i hi x)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_CountableGaussianReplicaIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replicaMean_varying_measurable {Ω : Type*} [MeasurableSpace Ω] {H : Ω → S → ℝ}
    {n : ℕ} {F : Ω → (Fin n → S) → ℝ} (hH : Measurable (Function.uncurry H))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun g => gibbsReplicaMean μ (H g) n (F g)) := by
  have hr : Measurable (fun p : Ω×(Fin n → S) => Real.exp (replicaPotential (H p.1) n p.2)) := by
    apply Measurable.exp
    exact Finset.measurable_sum _ fun i _ => hH.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  let ρ := Measure.pi fun _ : Fin n => μ
  have hn : Measurable (fun g => ∫ x, Real.exp (replicaPotential (H g) n x)*F g x ∂ρ) :=
    (hr.mul hF).stronglyMeasurable.integral_prod_right'.measurable
  have hd : Measurable (fun g => ∫ x, Real.exp (replicaPotential (H g) n x) ∂ρ) :=
    hr.stronglyMeasurable.integral_prod_right'.measurable
  unfold gibbsReplicaMean tiltMean tiltIntegral tiltPartition
  simp only [one_mul]
  convert hn.div hd using 1
  all_goals try with_reducible_and_instances rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma kernel_replicaMean_measurable {H : A → S → ℝ} {n : ℕ} {G : A → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G)) :
    Measurable (fun a => gibbsReplicaMean (κ a) (H a) n (G a)) := by
  change Measurable (fun a => tiltMean (kernelReplica κ n a) (replicaPotential (H a) n) (G a) 1)
  apply kernel_tiltMean_measurable (kernelReplica κ n) (H := fun a => replicaPotential (H a) n) _ hG
  change Measurable (fun a : A × (Fin n → S) => ∑ i, H a.1 (a.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma kernel_replicaMean_bounded_integrable (P : Measure A) [IsFiniteMeasure P]
    {H : A → S → ℝ} {n : ℕ} {G : A → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ a x, |G a x| ≤ B) :
    Integrable (fun a => gibbsReplicaMean (κ a) (H a) n (G a)) P := by
  apply Integrable.of_bound (kernel_replicaMean_measurable κ hH hG).aestronglyMeasurable B
  exact ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general (Measure.pi fun _ : Fin n => κ a)
      (replicaPotential_measurable hH.of_uncurry_left n) hG.of_uncurry_left hB (hGB a)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ContactGGRate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (H : A → S → ℝ)

lemma gibbsProbabilityKernel_replica_integral (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) (G : (Fin r → S) → ℝ) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) =
      gibbsReplicaMean (κ a) (H a) r G := by
  rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
  exact (gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi r G).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelInfiniteReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma infiniteReplica_prefix_preserving (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i : Fin r => x i.val)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin r => μ)) := by
  let e : (Finset.range r) ≃ Fin r :=
    { toFun := fun i => ⟨i.val,Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : MeasurePreserving ((Finset.range r).restrict : (ℕ → S) → (Finset.range r) → S)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : (Finset.range r) => μ)) :=
    ⟨by fun_prop,Measure.infinitePi_map_restrict _⟩
  have he := measurePreserving_piCongrLeft (fun _ : Fin r => μ) e
  exact he.comp hp

lemma kernelInfiniteReplica_prefix_integral (a : A) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) :
    (∫ x, G (fun i => x i.val) ∂kernelInfiniteReplica κ ℕ a) =
      ∫ x, G x ∂Measure.pi (fun _ : Fin r => κ a) := by
  have hp := infiniteReplica_prefix_preserving (κ a) r
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hG.aestronglyMeasurable]
  rfl

end

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma infinite_iid_reindex_preserving (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i => x (e i))
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => μ)) := by
  have he : (fun x : ℕ → S => fun i => x (e i)) = MeasurableEquiv.piCongrLeft (fun _ : ℕ => S) e.symm := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact ⟨(MeasurableEquiv.piCongrLeft _ e.symm).measurable,
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) e.symm⟩

end

lemma annealedInfiniteReplica_reindex {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
    (H : A → S → ℝ) (hH : Measurable (Function.uncurry H)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun a : A×(ℕ→S) => (a.1,fun i => a.2 (e i)))
      (annealedInfiniteReplicaMeasure κ P H hH) (annealedInfiniteReplicaMeasure κ P H hH) := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun x : ℕ→S => fun i => x (e i)) := by fun_prop
  have he : (kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map (fun x i => x (e i)) =
      kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ := by
    ext a s hs
    rw [Kernel.map_apply _ hm _]
    exact congrArg (fun μ : Measure (ℕ→S) => μ s)
      (infinite_iid_reindex_preserving (gibbsProbabilityKernel κ H a) e).map_eq
  refine ⟨by fun_prop, ?_⟩
  change (P ⊗ₘ kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map
    (Prod.map id (fun x i => x (e i))) = _
  rw [← Measure.compProd_map hm,he]
  rfl

lemma compactRelabel_continuous {K : Type*} [TopologicalSpace K] (e : Equiv.Perm ℕ) :
    Continuous (compactRelabel (K:=K) e) := by unfold compactRelabel; fun_prop

lemma compact_exchangeability_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    {μ : ℕ → ProbabilityMeasure (CompactArray K)} {ν : ProbabilityMeasure (CompactArray K)}
    (hμ : Tendsto μ atTop (𝓝 ν)) (e : Equiv.Perm ℕ)
    (he : ∀ n, MeasurePreserving (compactRelabel (K:=K) e) (μ n : Measure _) (μ n : Measure _)) :
    MeasurePreserving (compactRelabel (K:=K) e) (ν : Measure _) (ν : Measure _) := by
  have hc := compactRelabel_continuous (K:=K) e
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hc
  have he' (n : ℕ) : (μ n).map hc.measurable.aemeasurable = μ n := by
    apply Subtype.ext
    exact (he n).map_eq
  simp_rw [he'] at hmap
  have hv := tendsto_nhds_unique hmap hμ
  exact ⟨hc.measurable,congrArg Subtype.val hv⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkConcentration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkHamiltonian_section_measurable (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : BulkDisorder N M) : Measurable (bulkHamiltonian N M f v a.1 a.2) := by
  exact ((bulkHamiltonian_continuous N M f v).comp
    (continuous_const.prodMk continuous_id)).measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GibbsRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_restore {H W F : S→ℝ} (_hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) :
    tiltMean μ (fun x => H x+W x) F 1 =
      tiltMean μ H (fun x => Real.exp (W x)*F x) 1 /
        tiltMean μ H (fun x => Real.exp (W x)) 1 := by
  have hp : tiltPartition μ H 1≠0 :=
    (tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using hi)).ne'
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul,Real.exp_add,mul_assoc]
  have hp' : (∫ x, Real.exp (H x) ∂μ) ≠ 0 := by
    simpa only [tiltPartition,one_mul] using hp
  exact (div_div_div_cancel_right₀ hp' _ _).symm

lemma gibbsReplicaMean_fintype_prod {H F : S→ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) :
    gibbsReplicaMean μ H r (fun x => ∏ i, F (x i))=(tiltMean μ H F 1)^r := by
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  rw [gibbsReplicaMean_integral_of_integrable μ hH hi,
    ← tilt_law_integral_of_integrable μ hH hi']
  simpa only [Fintype.card_fin] using integral_fintype_prod_eq_pow (ι:=Fin r) F (μ:=tiltLaw μ H 1)

lemma gibbsReplicaMean_restore {H W : S→ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) (F : (Fin r→S)→ℝ) :
    gibbsReplicaMean μ (fun x => H x+W x) r F =
      gibbsReplicaMean μ H r (fun x => (∏ i, Real.exp (W (x i)))*F x) /
        (tiltMean μ H (fun x => Real.exp (W x)) 1)^r := by
  have hp : replicaPotential (fun x => H x+W x) r =
      fun x => replicaPotential H r x+replicaPotential W r x := by
    funext x; simp only [replicaPotential,Finset.sum_add_distrib]
  have hir : Integrable (fun x => Real.exp (replicaPotential H r x)) (Measure.pi fun _ : Fin r => μ) := by
    simpa only [one_mul] using (replica_exp_integrable μ
      (show Integrable (fun x => Real.exp (1*H x)) μ by simpa only [one_mul] using hi) r)
  unfold gibbsReplicaMean
  rw [hp,tiltMean_restore _ (replicaPotential_measurable hH r) hir]
  simp only [replicaPotential,Real.exp_sum]
  congr 1
  exact gibbsReplicaMean_fintype_prod μ (F:=fun x => Real.exp (W x)) hH hi r

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkFreshRestore
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma bulkSeparateLast_preserving (N M : ℕ) :
    MeasurePreserving (bulkSeparateLast N M) (bulkDisorderLaw N (M+1))
      ((bulkDisorderLaw N M).prod (stdGaussian (EuclideanSpace ℝ (Fin N)))) := by
  let ρ : Measure (Fin N→ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let R := finitePatternRowsLaw N M
  let G := stdGaussian (EuclideanSpace ℝ (Fin N))
  let B := stdGaussian (BulkMark N)
  have hrow : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→EuclideanSpace ℝ (Fin N)) ρ G :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hp := (((MeasurePreserving.id R).prod hrow).comp
    (Measure.measurePreserving_swap (μ:=ρ) (ν:=R))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (M+1) => ρ) (Fin.last M))
  have hr : MeasurePreserving (fun a : ((Fin M→Fin N→ℝ)×EuclideanSpace ℝ (Fin N))×BulkMark N =>
      ((a.1.1,a.2),a.1.2)) ((R.prod G).prod B) ((R.prod B).prod G) :=
    (measurePreserving_prodAssoc R B G).symm.comp
      (((MeasurePreserving.id R).prod (Measure.measurePreserving_swap (μ:=G) (ν:=B))).comp
        (measurePreserving_prodAssoc R G B))
  convert hr.comp (hp.prod (MeasurePreserving.id B)) using 1
  · funext a
    simp only [bulkSeparateLast,Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply]
    apply Prod.ext
    · apply Prod.ext
      · funext i j; simp [Fin.init]
      · rfl
    · rfl
  · rfl
  · rfl

lemma bulkHamiltonian_last (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder N (M+1)) (x : NormalizedSpin N) :
    bulkHamiltonian N (M+1) f v a.1 a.2 x =
      bulkHamiltonian N M f v (bulkSeparateLast N M a).1.1 (bulkSeparateLast N M a).1.2 x+
        f (inner ℝ x.val (bulkSeparateLast N M a).2) := by
  unfold bulkHamiltonian normalizedPatternEnergy
  rw [Fin.sum_univ_castSucc]
  simp only [bulkSeparateLast,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  ring

lemma bulkSeparateTwo_preserving (N M : ℕ) :
    MeasurePreserving (bulkSeparateTwo N M) (bulkDisorderLaw N (M+2))
      ((bulkDisorderLaw N M).prod
        ((stdGaussian (EuclideanSpace ℝ (Fin N))).prod (stdGaussian (EuclideanSpace ℝ (Fin N))))) := by
  exact (measurePreserving_prodAssoc _ _ _).comp
    (((bulkSeparateLast_preserving N M).prod (MeasurePreserving.id _)).comp
      (bulkSeparateLast_preserving N (M+1)))

lemma bulkHamiltonian_two (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder N (M+2)) (x : NormalizedSpin N) :
    bulkHamiltonian N (M+2) f v a.1 a.2 x =
      bulkHamiltonian N M f v (bulkSeparateTwo N M a).1.1 (bulkSeparateTwo N M a).1.2 x+
        (f (inner ℝ x.val (bulkSeparateTwo N M a).2.1)+
         f (inner ℝ x.val (bulkSeparateTwo N M a).2.2)) := by
  rw [bulkHamiltonian_last N (M+1),bulkHamiltonian_last N M]
  exact add_assoc _ _ _

lemma bulk_replica_restore_two (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) (M+2)) (r : ℕ) (F : (Fin r→NormalizedSpin (n+1))→ℝ) :
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+2) f v a.1 a.2) r F =
      gibbsReplicaMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v (bulkSeparateTwo (n+1) M a).1.1 (bulkSeparateTwo (n+1) M a).1.2) r
        (fun x => (∏ i, Real.exp (f (inner ℝ (x i).val (bulkSeparateTwo (n+1) M a).2.1)+
          f (inner ℝ (x i).val (bulkSeparateTwo (n+1) M a).2.2)))*F x) /
      (tiltMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v (bulkSeparateTwo (n+1) M a).1.1 (bulkSeparateTwo (n+1) M a).1.2)
        (fun x => Real.exp (f (inner ℝ x.val (bulkSeparateTwo (n+1) M a).2.1)+
          f (inner ℝ x.val (bulkSeparateTwo (n+1) M a).2.2))) 1)^r := by
  rw [show bulkHamiltonian (n+1) (M+2) f v a.1 a.2 = _ from
    funext (bulkHamiltonian_two (n+1) M f v a)]
  exact gibbsReplicaMean_restore _
    ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v _) r F

lemma bulkPermutePatterns_preserving (N M : ℕ) (e : Equiv.Perm (Fin M)) :
    MeasurePreserving (bulkPermutePatterns N M e) (bulkDisorderLaw N M) (bulkDisorderLaw N M) := by
  have h := (measurePreserving_piCongrLeft
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)) e.symm).prod
    (MeasurePreserving.id (stdGaussian (BulkMark N)))
  convert h using 1
  · funext a
    apply Prod.ext
    · funext i
      have he := MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : Fin M => Fin N→ℝ) e.symm a.1 (e i)
      change a.1 (e i) = (MeasurableEquiv.piCongrLeft (fun _ : Fin M => Fin N→ℝ) e.symm) a.1 i
      simpa only [Equiv.symm_apply_apply] using he.symm
    · rfl
  · rfl
  · rfl

lemma bulkHamiltonian_permute (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (e : Equiv.Perm (Fin M)) (a : BulkDisorder N M) :
    bulkHamiltonian N M f v (bulkPermutePatterns N M e a).1 (bulkPermutePatterns N M e a).2 =
      bulkHamiltonian N M f v a.1 a.2 := by
  funext x
  unfold bulkHamiltonian normalizedPatternEnergy bulkPermutePatterns
  congr 1
  exact Equiv.sum_comp e (fun j => f (∑ i, a.1 j i*x.val i))

lemma bulkReplicaMean_permute (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (e : Equiv.Perm (Fin M))
    (F : BulkDisorder (n+1) M → (Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) :
    bulkReplicaMean n M f v r (fun a => F (bulkPermutePatterns (n+1) M e a)) =
      bulkReplicaMean n M f v r F := by
  have hm := kernel_replicaMean_measurable (bulkSpinKernel n M)
    (H:=fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous (n+1) M f v).measurable hF
  have h := integral_map (μ:=bulkDisorderLaw (n+1) M) (bulkPermutePatterns_preserving (n+1) M e).measurable.aemeasurable
    hm.aestronglyMeasurable
  rw [(bulkPermutePatterns_preserving (n+1) M e).map_eq] at h
  change (∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (F a) ∂bulkDisorderLaw (n+1) M) = _ at h
  unfold bulkReplicaMean
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    change gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r _ =
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v (bulkPermutePatterns (n+1) M e a).1 (bulkPermutePatterns (n+1) M e a).2) r _
    rw [bulkHamiltonian_permute]

lemma bulk_row_exchange (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T : (Fin r→ℝ)→ℝ) (hT : Measurable T) (i j : Fin M) :
    bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields i a x)) =
      bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields j a x)) := by
  classical
  have hm : Measurable (Function.uncurry (fun a x => G x*T (bulkPatternFields j a x))) :=
    (hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _))
  have h := bulkReplicaMean_permute n M f v r (Equiv.swap i j) _ hm
  have hf : (fun a x => G x*T (bulkPatternFields j (bulkPermutePatterns (n+1) M (Equiv.swap i j) a) x)) =
      (fun a x => G x*T (bulkPatternFields i a x)) := by
    funext a x
    change G x*T (fun l => ∑ t, a.1 ((Equiv.swap i j) j) t*(x l).val t) =
      G x*T (fun l => ∑ t, a.1 i t*(x l).val t)
    rw [Equiv.swap_apply_right]
  rw [hf] at h
  exact h

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundedGibbsDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma bounded_gibbs_integral_deriv
    {H H' F F' : ℝ → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ t x, |H t x| ≤ A) (hHB : ∀ t x, |H' t x| ≤ B)
    (hFC : ∀ t x, |F t x| ≤ C) (hFD : ∀ t x, |F' t x| ≤ D)
    (hdH : ∀ t x, HasDerivAt (fun u => H u x) (H' t x) t)
    (hdF : ∀ t x, HasDerivAt (fun u => F u x) (F' t x) t) (t : ℝ) :
    HasDerivAt (fun u => tiltIntegral μ (H u) (F u) 1)
      (∫ x, Real.exp (H t x) * (H' t x * F t x + F' t x) ∂μ) t := by
  simp only [tiltIntegral, one_mul]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u x => Real.exp (H u x)*F u x)
    (s := univ) (bound := fun _ => Real.exp A * (B*C+D))
    (F' := fun u x => Real.exp (H u x) * (H' u x * F u x+F' u x))
    (Filter.univ_mem) (Eventually.of_forall fun u =>
      ((hH.comp (measurable_const.prodMk measurable_id)).exp.mul
        (hF.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    (by
      simpa only [one_mul, Function.comp_def, Function.uncurry_def, id_eq, Pi.mul_apply] using tilt_integrable μ
        (hH.comp (measurable_const.prodMk measurable_id))
        (hF.comp (measurable_const.prodMk measurable_id)) hA hC (hHA t) (hFC t) 1)
    (by fun_prop) (ae_of_all _ fun x u _ => ?_) (integrable_const _)
    (ae_of_all _ fun x u _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm (Real.exp (H u x)), mul_comm (Real.exp A)]
    apply mul_le_mul _ (Real.exp_le_exp.mpr ((le_abs_self _).trans (hHA u x)))
      (Real.exp_pos _).le (add_nonneg (mul_nonneg hB hC) hD)
    exact (abs_add_le _ _).trans (add_le_add (by
      rw [abs_mul]; exact mul_le_mul (hHB u x) (hFC u x) (abs_nonneg _) hB) (hFD u x))
  · convert! ((hdH u x).exp.mul (hdF u x)) using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma bounded_gibbs_mean_deriv
    {H H' F F' : ℝ → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ t x, |H t x| ≤ A) (hHB : ∀ t x, |H' t x| ≤ B)
    (hFC : ∀ t x, |F t x| ≤ C) (hFD : ∀ t x, |F' t x| ≤ D)
    (hdH : ∀ t x, HasDerivAt (fun u => H u x) (H' t x) t)
    (hdF : ∀ t x, HasDerivAt (fun u => F u x) (F' t x) t) (t : ℝ) :
    HasDerivAt (fun u => tiltMean μ (H u) (F u) 1)
      (tiltMean μ (H t) (fun x => H' t x * F t x+F' t x) 1 -
        tiltMean μ (H t) (F t) 1 * tiltMean μ (H t) (H' t) 1) t := by
  have hnum := bounded_gibbs_integral_deriv μ hH hH' hF hF' hA hB hC hD
    hHA hHB hFC hFD hdH hdF t
  have hden := bounded_gibbs_integral_deriv μ hH hH' (F := fun _ _ => 1)
    (F' := fun _ _ => 0) (C := 1) (D := 0) measurable_const measurable_const hA hB (by norm_num)
    (by norm_num) hHA hHB (by simp) (by simp) hdH (by intro t x; exact hasDerivAt_const _ _) t
  simp only [mul_one, add_zero, tiltIntegral, one_mul] at hden
  have hp := (tilt_partition_pos μ (hH.comp (measurable_const.prodMk measurable_id))
    hA (hHA t) 1).ne'
  have hp' : (∫ x, Real.exp (H t x) ∂μ) ≠ 0 := by
    simpa only [tiltPartition, one_mul, Function.comp_def, Function.uncurry_def, id_eq] using hp
  convert! hnum.div hden hp' using 1
  · simp only [tiltMean, tiltPartition, one_mul, Pi.div_def]
  · simp only [tiltMean, tiltIntegral, tiltPartition, one_mul]
    field_simp [hp']

lemma bounded_gaussian_gibbs_coordinate_ibp {n : ℕ} (i : Fin (n+1))
    {H H' F F' : (Fin (n+1) → ℝ) → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ g x, |H g x| ≤ A) (hHB : ∀ g x, |H' g x| ≤ B)
    (hFC : ∀ g x, |F g x| ≤ C) (hFD : ∀ g x, |F' g x| ≤ D)
    (hdH : ∀ g t x, HasDerivAt (fun u => H (i.insertNth u g) x) (H' (i.insertNth t g) x) t)
    (hdF : ∀ g t x, HasDerivAt (fun u => F (i.insertNth u g) x) (F' (i.insertNth t g) x) t) :
    (∫ g, g i * tiltMean μ (H g) (F g) 1 ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, tiltMean μ (H g) (fun x => H' g x*F g x+F' g x) 1 -
        tiltMean μ (H g) (F g) 1 * tiltMean μ (H g) (H' g) 1
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hm := measurable_tiltMean_param μ hH hF
  have hmm := measurable_tiltMean_param μ (Y := fun g x => H' g x*F g x+F' g x) hH ((hH'.mul hF).add hF')
  have hm' := measurable_tiltMean_param μ hH hH'
  have hb (g) := tilt_mean_bound μ
    (hH.comp (measurable_const.prodMk measurable_id))
    (hF.comp (measurable_const.prodMk measurable_id)) hA hC (hHA g) (hFC g) 1
  have hb' (g) := tilt_mean_bound μ
    (hH.comp (measurable_const.prodMk measurable_id))
    (hH'.comp (measurable_const.prodMk measurable_id)) hA hB (hHA g) (hHB g) 1
  apply gaussian_pi_coordinate_integrationByParts n i hm (hmm.sub (hm.mul hm'))
    (C := C) (B := 2*B*C+D) hb
  · intro g
    have hab (x) : |H' g x*F g x+F' g x| ≤ B*C+D :=
      (abs_add_le _ _).trans (add_le_add (by
        rw [abs_mul]; exact mul_le_mul (hHB g x) (hFC g x) (abs_nonneg _) hB) (hFD g x))
    have hj := tilt_mean_bound μ
      (hH.comp (measurable_const.prodMk measurable_id))
      (((hH'.mul hF).add hF').comp (measurable_const.prodMk measurable_id))
      hA (by positivity) (hHA g) hab 1
    exact (abs_sub _ _).trans (by
      simp only [Pi.mul_apply, abs_mul]
      have hp := mul_le_mul (hb g) (hb' g) (abs_nonneg _) hC
      simp only [Function.comp_def, Function.uncurry_def, id_eq, Pi.add_apply, Pi.mul_apply] at hj hp
      nlinarith)
  · intro g t
    have he : Measurable (fun p : ℝ×S => ((i.insertNth p.1 g : Fin (n+1) → ℝ),p.2)) := by
      fun_prop
    exact bounded_gibbs_mean_deriv μ
      (H := fun t x => H (i.insertNth t g) x)
      (H' := fun t x => H' (i.insertNth t g) x)
      (F := fun t x => F (i.insertNth t g) x)
      (F' := fun t x => F' (i.insertNth t g) x)
      (hH.comp he) (hH'.comp he) (hF.comp he) (hF'.comp he)
      hA hB hC hD (fun u => hHA _) (fun u => hHB _) (fun u => hFC _) (fun u => hFD _)
      (hdH g) (hdF g) t

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_NonlinearReplicaIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma bounded_gaussian_replica_coordinate_ibp {m n : ℕ} (i : Fin (m+1))
    {H H' : (Fin (m+1) → ℝ) → S → ℝ}
    {F F' : (Fin (m+1) → ℝ) → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ g x, |H g x| ≤ A) (hHB : ∀ g x, |H' g x| ≤ B)
    (hFC : ∀ g x, |F g x| ≤ C) (hFD : ∀ g x, |F' g x| ≤ D)
    (hdH : ∀ g t x, HasDerivAt (fun u => H (i.insertNth u g) x) (H' (i.insertNth t g) x) t)
    (hdF : ∀ g t x, HasDerivAt (fun u => F (i.insertNth u g) x) (F' (i.insertNth t g) x) t) :
    (∫ g, g i * gibbsReplicaMean μ (H g) n (F g)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
        (fun x => replicaPotential (H' g) n x*F g x+F' g x) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => H' g (x 0)*F g (fun j => x j.succ))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hr (J : (Fin (m+1) → ℝ) → S → ℝ)
      (hJ : Measurable (Function.uncurry J)) :
      Measurable (Function.uncurry (fun g => replicaPotential (J g) n)) := by
    change Measurable (fun p : (Fin (m+1) → ℝ)×(Fin n → S) => ∑ j : Fin n, J p.1 (p.2 j))
    exact Finset.measurable_sum _ fun j _ => hJ.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have he := bounded_gaussian_gibbs_coordinate_ibp (Measure.pi (fun _ : Fin n => μ)) i
    (hr H hH) (hr H' hH') hF hF' (by positivity) (by positivity) hC hD
    (fun g => replicaPotential_bound (hHA g) n)
    (fun g => replicaPotential_bound (hHB g) n) hFC hFD
    (fun g t x => HasDerivAt.fun_sum fun j _ => hdH g t (x j)) hdF
  refine he.trans ?_
  apply integral_congr_ae
  filter_upwards [] with g
  have hm : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  have hm' : Measurable (H' g) := hH'.comp (measurable_const.prodMk measurable_id)
  have fm : Measurable (F g) := hF.comp (measurable_const.prodMk measurable_id)
  rw [tilt_replica_sum μ hm hm' hA (hHA g) (hHB g) n 1]
  simp only [gibbsReplicaMean]
  rw [tilt_replica_new_product μ hm hm' fm hA (hHA g) (hHB g) (hFC g) 1]
  change _ - _ * ((n:ℝ)*_) = _ - (n:ℝ)*(_*_)
  ring

lemma nonlinear_pattern_replica_coordinate_ibp {m n : ℕ} (i : Fin (m+1)) (j : Fin n)
    (f : Jet3) {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {U : (Fin n → S) → ℝ}
    (hv : ∀ l, Measurable (v l)) (hh : Measurable h) (hU : Measurable U)
    {A C D : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhA : ∀ x, |h x| ≤ A) (hvC : ∀ l x, |v l x| ≤ C) (hUD : ∀ x, |U x| ≤ D) :
    let b := gaussianField (m+1) v
    let H := fun g x => h x+f.f (b g x)
    (∫ g, g i*gibbsReplicaMean μ (H g) n (fun x => f.d1 (b g (x j))*U x)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
        (fun x => ((∑ l, f.d1 (b g (x l))*v i (x l))*f.d1 (b g (x j))+
          f.d2 (b g (x j))*v i (x j))*U x) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => f.d1 (b g (x 0))*v i (x 0)*
          (f.d1 (b g (x j.succ))*U (fun l => x l.succ)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let b := gaussianField (m+1) v
  let H := fun g x => h x+f.f (b g x)
  let H' := fun g x => f.d1 (b g x)*v i x
  let F := fun g (x : Fin n → S) => f.d1 (b g (x j))*U x
  let F' := fun g (x : Fin n → S) => f.d2 (b g (x j))*v i (x j)*U x
  have hb : Measurable (Function.uncurry b) := gaussianField_measurable hv
  have hb' : Measurable (fun p : (Fin (m+1) → ℝ)×(Fin n → S) => b p.1 (p.2 j)) :=
    hb.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hHm : Measurable (Function.uncurry H) :=
    (hh.comp measurable_snd).add (f.f.continuous.measurable.comp hb)
  have hH'm : Measurable (Function.uncurry H') :=
    (f.d1.continuous.measurable.comp hb).mul ((hv i).comp measurable_snd)
  have hFm : Measurable (Function.uncurry F) :=
    (f.d1.continuous.measurable.comp hb').mul (hU.comp measurable_snd)
  have hF'm : Measurable (Function.uncurry F') :=
    ((f.d2.continuous.measurable.comp hb').mul
      ((hv i).comp ((measurable_pi_apply j).comp measurable_snd))).mul (hU.comp measurable_snd)
  have hHA (g x) : |H g x| ≤ A+‖f.f‖ :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (f.f.norm_coe_le_norm _))
  have hHB (g x) : |H' g x| ≤ ‖f.d1‖*C := by
    dsimp only [H']
    rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i x) (abs_nonneg _) (norm_nonneg _)
  have hFC (g x) : |F g x| ≤ ‖f.d1‖*D := by
    dsimp only [F]
    rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hUD x) (abs_nonneg _) (norm_nonneg _)
  have hFD (g x) : |F' g x| ≤ ‖f.d2‖*C*D := by
    dsimp only [F']
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (f.d2.norm_coe_le_norm _) (hvC i _)
      (abs_nonneg _) (norm_nonneg _)) (hUD _) (abs_nonneg _) (by positivity)
  have hdH (g t x) : HasDerivAt (fun s => H (i.insertNth s g) x)
      (H' (i.insertNth t g) x) t := by
    dsimp [H,H',b]
    simp_rw [gaussianField_insertNth]
    convert! ((f.has1 _).comp t (((hasDerivAt_id t).mul_const (v i x)).add_const
      (gaussianField m (fun l => v (i.succAbove l)) g x))).const_add (h x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul,id_eq]
  have hdF (g t x) : HasDerivAt (fun s => F (i.insertNth s g) x)
      (F' (i.insertNth t g) x) t := by
    dsimp [F,F',b]
    simp_rw [gaussianField_insertNth]
    convert! (((f.has2 _).comp t (((hasDerivAt_id t).mul_const (v i (x j))).add_const
      (gaussianField m (fun l => v (i.succAbove l)) g (x j)))).mul_const (U x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul,id_eq]
  have he := bounded_gaussian_replica_coordinate_ibp μ i hHm hH'm hFm hF'm
    (by positivity) (by positivity) (by positivity) (by positivity) hHA hHB hFC hFD hdH hdF
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with g
  congr 2
  funext x
  dsimp only [H', F, F', replicaPotential, b]
  ring
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_NonlinearDirectionIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma nonlinear_pattern_direction_ibp {m n : ℕ} (j : Fin n) (f : Jet3)
    {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {w : Fin (m+1) → (Fin n → S) → ℝ}
    (hv : ∀ i, Measurable (v i)) (hh : Measurable h) (hw : ∀ i, Measurable (w i))
    {A C D : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhA : ∀ x, |h x| ≤ A) (hvC : ∀ i x, |v i x| ≤ C) (hwD : ∀ i x, |w i x| ≤ D) :
    let b := gaussianField (m+1) v
    let H := fun g x => h x+f.f (b g x)
    let K := fun (x : Fin n→S) y => ∑ i, w i x*v i y
    (∫ g, gibbsReplicaMean μ (H g) n
      (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
      (fun x => (∑ l, f.d1 (b g (x l))*f.d1 (b g (x j))*K x (x l))+
        f.d2 (b g (x j))*K x (x j)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => f.d1 (b g (x 0))*f.d1 (b g (x j.succ))*K (fun l => x l.succ) (x 0))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin (m+1) => gaussianReal 0 1)
  let b := gaussianField (m+1) v
  let H := fun g x => h x+f.f (b g x)
  let F := fun i g (x : Fin n→S) => f.d1 (b g (x j))*w i x
  let U := fun i g (x : Fin n→S) =>
    ((∑ l, f.d1 (b g (x l))*v i (x l))*f.d1 (b g (x j))+
      f.d2 (b g (x j))*v i (x j))*w i x
  let V := fun i g (x : Fin (n+1)→S) =>
    f.d1 (b g (x 0))*v i (x 0)*(f.d1 (b g (x j.succ))*w i (fun l => x l.succ))
  have hb : Measurable (Function.uncurry b) := gaussianField_measurable hv
  have hH : Measurable (Function.uncurry H) :=
    (hh.comp measurable_snd).add (f.f.continuous.measurable.comp hb)
  have hHA (g x) : |H g x| ≤ A+‖f.f‖ :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (f.f.norm_coe_le_norm _))
  have he (r : ℕ) (i : Fin r) : Measurable
      (fun p : (Fin (m+1)→ℝ)×(Fin r→S) => b p.1 (p.2 i)) :=
    hb.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hFm (i) : Measurable (Function.uncurry (F i)) :=
    (f.d1.measurable.comp (he n j)).mul ((hw i).comp measurable_snd)
  have hUm (i) : Measurable (Function.uncurry (U i)) := by
    exact (((Finset.measurable_sum _ fun l _ => (f.d1.measurable.comp (he n l)).mul
      ((hv i).comp ((measurable_pi_apply l).comp measurable_snd))).mul
      (f.d1.measurable.comp (he n j))).add ((f.d2.measurable.comp (he n j)).mul
      ((hv i).comp ((measurable_pi_apply j).comp measurable_snd)))).mul ((hw i).comp measurable_snd)
  have hVm (i) : Measurable (Function.uncurry (V i)) := by
    exact ((f.d1.measurable.comp (he (n+1) 0)).mul
      ((hv i).comp ((measurable_pi_apply 0).comp measurable_snd))).mul
      ((f.d1.measurable.comp (he (n+1) j.succ)).mul
        ((hw i).comp ((Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ).comp measurable_snd)))
  have hFB (i g x) : |F i g x| ≤ ‖f.d1‖*D := by
    dsimp [F]; rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hwD i x) (abs_nonneg _) (norm_nonneg _)
  have hsB (i g) (x : Fin n→S) : |∑ l, f.d1 (b g (x l))*v i (x l)| ≤ n*(‖f.d1‖*C) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin n, ‖f.d1‖*C := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]; exact mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp
  have hUB (i g x) : |U i g x| ≤ ((n:ℝ)*(‖f.d1‖*C)*‖f.d1‖+‖f.d2‖*C)*D := by
    dsimp only [U]; rw [abs_mul]
    apply mul_le_mul _ (hwD i x) (abs_nonneg _) (by positivity)
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul]; exact mul_le_mul (hsB i g x) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (by positivity)
    · rw [abs_mul]; exact mul_le_mul (f.d2.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _)
  have hVB (i g x) : |V i g x| ≤ (‖f.d1‖*C)*(‖f.d1‖*D) := by
    dsimp only [V]; rw [abs_mul,abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul (f.d1.norm_coe_le_norm _) (hwD i _) (abs_nonneg _) (norm_nonneg _)) (by positivity) (by positivity)
  have hiU (i) : Integrable (fun g => gibbsReplicaMean μ (H g) n (U i g)) γ := by
    apply Integrable.of_bound (replicaMean_varying_measurable μ hH (hUm i)).aestronglyMeasurable
      (((n:ℝ)*(‖f.d1‖*C)*‖f.d1‖+‖f.d2‖*C)*D)
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hUm i).of_uncurry_left
        (by positivity) (by positivity) (hHA g) (hUB i g)
  have hiV (i) : Integrable (fun g => gibbsReplicaMean μ (H g) (n+1) (V i g)) γ := by
    apply Integrable.of_bound (replicaMean_varying_measurable μ hH (hVm i)).aestronglyMeasurable
      ((‖f.d1‖*C)*(‖f.d1‖*D))
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hVm i).of_uncurry_left
        (by positivity) (by positivity) (hHA g) (hVB i g)
  have hiF (i) : Integrable (fun g => g i*gibbsReplicaMean μ (H g) n (F i g)) γ := by
    have hg : Integrable (fun g : Fin (m+1)→ℝ => g i) γ :=
      ((measurePreserving_eval (fun _ : Fin (m+1) => gaussianReal 0 1) i).integrable_comp
        measurable_id.aestronglyMeasurable).mpr
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    exact hg.mul_bdd (replicaMean_varying_measurable μ hH (hFm i)).aestronglyMeasurable
      (ae_of_all _ fun g => by
        simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hFm i).of_uncurry_left
          (by positivity) (by positivity) (hHA g) (hFB i g))
  have hl (g) : gibbsReplicaMean μ (H g) n (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x)) =
      ∑ i, g i*gibbsReplicaMean μ (H g) n (F i g) := by
    rw [show (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x)) = (fun x => ∑ i, g i*F i g x) by
      funext x; simp only [Finset.mul_sum,F]; apply Finset.sum_congr rfl; intros; ring]
    rw [replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hFm i).of_uncurry_left.const_mul (g i))
      (by positivity) (hHA g) (D := fun i => |g i| *(‖f.d1‖*D)) (fun i _ x => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFB i g x) (abs_nonneg _))]
    simp_rw [replicaMean_const_mul]
  have hr (g) : (∑ i, (gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g))) =
      gibbsReplicaMean μ (H g) n (fun x =>
        (∑ l, f.d1 (b g (x l))*f.d1 (b g (x j))*(∑ i, w i x*v i (x l)))+
        f.d2 (b g (x j))*(∑ i, w i x*v i (x j))) -
      n*gibbsReplicaMean μ (H g) (n+1) (fun x =>
        f.d1 (b g (x 0))*f.d1 (b g (x j.succ))*(∑ i, w i (fun l => x l.succ)*v i (x 0))) := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,
      ←replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hUm i).of_uncurry_left)
        (by positivity) (hHA g) (fun i _ => hUB i g),
      ←replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hVm i).of_uncurry_left)
        (by positivity) (hHA g) (fun i _ => hVB i g)]
    congr 1
    · congr 1; funext x
      simp only [U,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1 <;> (apply Finset.sum_congr rfl; intro i _)
      · apply Finset.sum_congr rfl; intros; ring
      · ring
    · congr 1; congr 1; funext x
      simp only [V,Finset.mul_sum]
      apply Finset.sum_congr rfl; intros; ring
  calc
    _ = ∫ g, ∑ i, g i*gibbsReplicaMean μ (H g) n (F i g) ∂γ := integral_congr_ae (ae_of_all _ hl)
    _ = _ := by
      rw [integral_finsetSum _ fun i _ => hiF i]
      simp_rw [show ∀ i, (∫ g, g i*gibbsReplicaMean μ (H g) n (F i g) ∂γ) =
          ∫ g, gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g) ∂γ
        from fun i => nonlinear_pattern_replica_coordinate_ibp μ i j f hv hh (hw i) hA hC hD hhA hvC (hwD i)]
      rw [←integral_finsetSum Finset.univ (f := fun i g =>
        gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g))
        (fun i _ => (hiU i).sub ((hiV i).const_mul n))]
      exact integral_congr_ae (ae_of_all _ hr)
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_SphericalPatternDirection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma spinOverlap_self {N : ℕ} (x : NormalizedSpin N) : spinOverlap x x = 1 := by
  have hx : ‖x.val‖ = 1 := by simp
  simp [spinOverlap,hx]

lemma spinOverlap_sum {N : ℕ} (x y : NormalizedSpin N) :
    spinOverlap x y = ∑ i, x.val i*y.val i := by
  simp [spinOverlap,PiLp.inner_apply,mul_comm]

lemma normalizedSpin_coord_bound {N : ℕ} (x : NormalizedSpin N) (i : Fin N) : |x.val i| ≤ 1 := by
  have hx : ‖x.val‖ = 1 := by simp
  simpa only [Real.norm_eq_abs,hx] using PiLp.norm_apply_le x.val i

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkReplicaDominated
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma replicaMean_param_integrable_dominated {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure Ω) (r : ℕ)
    {H : Ω→S→ℝ} {F : Ω→(Fin r→S)→ℝ}
    (hH : Measurable (Function.uncurry H)) (hF : Measurable (Function.uncurry F))
    {D : Ω→ℝ} (hD : Integrable D ν) (hD0 : ∀ a,0≤D a) (hb : ∀ a x,|F a x|≤D a) :
    Integrable (fun a => gibbsReplicaMean μ (H a) r (F a)) ν := by
  apply hD.mono' (measurable_replicaMean_param μ hH hF).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    rw [Real.norm_eq_abs]
    exact tiltMean_bound_general _ (replicaPotential_measurable hH.of_uncurry_left r)
      hF.of_uncurry_left (hD0 a) (hb a)

lemma normalizedSpin_inner_bound {N : ℕ} (x : NormalizedSpin N) (b : Spin N) :
    |inner ℝ x.val b|≤‖b‖ := by
  have hx : ‖x.val‖=1 := by simp
  simpa only [hx,one_mul] using abs_real_inner_le_norm x.val b

lemma bulkFreshReplicaMean_integrable (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) {D : Spin (n+1)→ℝ}
    (hD : Integrable D (stdGaussian (Spin (n+1)))) (hD0 : ∀ b,0≤D b) (hb : ∀ b x,|F b x|≤D b) :
    Integrable (fun p : BulkDisorder (n+1) M×Spin (n+1) =>
      gibbsReplicaMean (unitSphereLaw (n+1))
        (fun x => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x+f (inner ℝ x.val p.2)) r (F p.2))
      ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) := by
  apply replicaMean_param_integrable_dominated _ _ r _ _ (hD.comp_snd _) (fun p => hD0 p.2) (fun p x => hb p.2 x)
  · exact ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_fst.fst.prodMk measurable_snd)).add
      (f.continuous.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd))
  · exact hF.comp (measurable_fst.snd.prodMk measurable_snd)

lemma bulkReplicaMean_last_integral (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) {D : Spin (n+1)→ℝ}
    (hD : Integrable D (stdGaussian (Spin (n+1)))) (hD0 : ∀ b,0≤D b) (hb : ∀ b x,|F b x|≤D b) :
    bulkReplicaMean n (M+1) f v r (fun a x => F (bulkSeparateLast (n+1) M a).2 x)=
      ∫ a : BulkDisorder (n+1) M, ∫ b : Spin (n+1),
        gibbsReplicaMean (unitSphereLaw (n+1))
          (fun x => bulkHamiltonian (n+1) M f v a.1 a.2 x+f (inner ℝ x.val b)) r (F b)
          ∂stdGaussian (Spin (n+1)) ∂bulkDisorderLaw (n+1) M := by
  let H := fun p : BulkDisorder (n+1) M×Spin (n+1) =>
    fun x : NormalizedSpin (n+1) => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x+f (inner ℝ x.val p.2)
  have hH : Measurable (Function.uncurry H) := by
    exact ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_fst.fst.prodMk measurable_snd)).add
      (f.continuous.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd))
  have hFm : Measurable (Function.uncurry (fun p : BulkDisorder (n+1) M×Spin (n+1) => F p.2)) :=
    hF.comp (measurable_fst.snd.prodMk measurable_snd)
  have hm := measurable_replicaMean_param (unitSphereLaw (n+1)) hH hFm
  have hi := bulkFreshReplicaMean_integrable n M r f v F hF hD hD0 hb
  have he := integral_map (μ := bulkDisorderLaw (n+1) (M+1)) (bulkSeparateLast_preserving (n+1) M).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(bulkSeparateLast_preserving (n+1) M).map_eq] at he
  change (∫ a : BulkDisorder (n+1) (M+1),
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+1) f v a.1 a.2) r
      (F (bulkSeparateLast (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+1))=_
  calc
    _ = ∫ a : BulkDisorder (n+1) (M+1),
        gibbsReplicaMean (unitSphereLaw (n+1)) (H (bulkSeparateLast (n+1) M a)) r
          (F (bulkSeparateLast (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+1) := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => by
        have hham : bulkHamiltonian (n+1) (M+1) f v a.1 a.2 = H (bulkSeparateLast (n+1) M a) := by
          funext x
          exact bulkHamiltonian_last (n+1) M f v a x
        exact congrArg (fun h => gibbsReplicaMean (unitSphereLaw (n+1)) h r (F (bulkSeparateLast (n+1) M a).2)) hham
    _ = ∫ p : BulkDisorder (n+1) M×Spin (n+1),
        gibbsReplicaMean (unitSphereLaw (n+1)) (H p) r (F p.2)
          ∂(bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1))) := he.symm
    _ = _ := integral_prod _ hi

lemma bulkReplicaMean_row_eq_last (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (j : Fin (M+1))
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ) (hF : Measurable (Function.uncurry F)) :
    bulkReplicaMean n (M+1) f v r (fun a => F (WithLp.toLp 2 (a.1 j))) =
      bulkReplicaMean n (M+1) f v r (fun a => F (bulkSeparateLast (n+1) M a).2) := by
  classical
  have hm : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) (M+1) => F (bulkSeparateLast (n+1) M a).2)) :=
    hF.comp (((bulkSeparateLast_preserving (n+1) M).measurable.snd.comp measurable_fst).prodMk measurable_snd)
  have he := bulkReplicaMean_permute n (M+1) f v r (Equiv.swap j (Fin.last M))
    (fun a => F (bulkSeparateLast (n+1) M a).2) hm
  simpa only [bulkSeparateLast,bulkPermutePatterns,Equiv.swap_apply_right] using he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_GaussianReplicaFubini
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S E : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
  [SecondCountableTopology S] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_joint_continuous {r : ℕ} {v : S→E} (hv : Continuous v) :
    Continuous (fun p : E×(Fin r→S) => gaussianRows (fun i => v (p.2 i)) p.1) := by
  change Continuous (fun p : E×(Fin r→S) => WithLp.toLp 2 (fun i => inner ℝ (v (p.2 i)) p.1))
  fun_prop

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_RestorationReplicaBlocks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma restorationReplicaTest_twoMarks {N r : ℕ} (f : ℝ→ᵇℝ)
    (F : CompactBlock CompactOverlap r→ᵇℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r)→ᵇℝ)
    (z₁ z₂ : EuclideanSpace ℝ (Fin N)) (k : ℕ) (x : Fin (r+k)→NormalizedSpin N) :
    restorationReplicaTest r (fun x : NormalizedSpin N => Real.exp (f (inner ℝ x.val z₁)+f (inner ℝ x.val z₂)))
      (fun x => (∏ i, Real.exp (f (inner ℝ (x i).val z₁)+f (inner ℝ (x i).val z₂)))*
        F (fun i j => bulkOverlap (x i) (x j))*Ψ (gaussianRows (fun i => (x i).val) z₁)*
          Φ (gaussianRows (fun i => (x i).val) z₂)) k x =
      restorationBlockTest r F k (fun i j => bulkOverlap (x i) (x j))*
        restorationMarkTest r f Ψ k (gaussianRows (fun i => (x i).val) z₁)*
        restorationMarkTest r f Φ k (gaussianRows (fun i => (x i).val) z₂) := by
  induction k with
  | zero =>
    simp only [restorationReplicaTest,restorationBlockTest,restorationMarkTest,
      BoundedContinuousFunction.mul_apply, gaussianReplicaTest, BoundedContinuousFunction.prod_apply,
      BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, expBCF_apply,one_mul,
      gaussianRows_apply,Real.exp_add,Finset.prod_mul_distrib]
    ring_nf
    rfl
  | succ k hk =>
    change Real.exp (f (inner ℝ (x 0).val z₁)+f (inner ℝ (x 0).val z₂))*
      restorationReplicaTest r _ _ k (fun i => x i.succ) = _
    rw [hk,Real.exp_add]
    change Real.exp (f (inner ℝ (x 0).val z₁))*Real.exp (f (inner ℝ (x 0).val z₂))*
      (restorationBlockTest r F k (fun i j => bulkOverlap (x i.succ) (x j.succ))*
        restorationMarkTest r f Ψ k (gaussianRows (fun i => (x i.succ).val) z₁)*
        restorationMarkTest r f Φ k (gaussianRows (fun i => (x i.succ).val) z₂)) =
      restorationBlockTest r F k (fun i j => bulkOverlap (x i.succ) (x j.succ))*
        (Real.exp (1*f (inner ℝ (x 0).val z₁))*restorationMarkTest r f Ψ k
          (gaussianRows (fun i => (x i.succ).val) z₁))*
        (Real.exp (1*f (inner ℝ (x 0).val z₂))*restorationMarkTest r f Φ k
          (gaussianRows (fun i => (x i.succ).val) z₂))
    simp only [one_mul]
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRestoredObservables
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkMarkedTest_continuous (N r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Continuous (Function.uncurry (bulkMarkedTest N r F Ψ Φ)) := by
  have hF : Continuous (fun x : Fin r → NormalizedSpin N => F (fun i j => bulkOverlap (x i) (x j))) := by
    apply F.continuous.comp
    unfold bulkOverlap spinOverlap
    fun_prop
  have hv : Continuous (fun x : NormalizedSpin N => x.val) := continuous_subtype_val
  have hg : Continuous (fun p : EuclideanSpace ℝ (Fin N) × (Fin r → NormalizedSpin N) =>
      gaussianRows (fun i => (p.2 i).val) p.1) :=
    gaussianRows_joint_continuous hv
  have hp₁ : Continuous (fun p : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) ×
      (Fin r → NormalizedSpin N) => (p.1.1,p.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  have hp₂ : Continuous (fun p : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) ×
      (Fin r → NormalizedSpin N) => (p.1.2,p.2)) :=
    continuous_fst.snd.prodMk continuous_snd
  have h₁ := Ψ.continuous.comp (hg.comp hp₁)
  have h₂ := Φ.continuous.comp (hg.comp hp₂)
  exact ((hF.comp continuous_snd).mul h₁).mul h₂

lemma twoFreshHamiltonian_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) :
    Measurable (fun p : TwoFreshDisorder (n+1) M × NormalizedSpin (n+1) =>
      bulkHamiltonian (n+1) M f v p.1.1.1 p.1.1.2 p.2) := by
  have hp : Continuous (fun p : TwoFreshDisorder (n+1) M × NormalizedSpin (n+1) =>
      (p.1.1,p.2)) := continuous_fst.fst.prodMk continuous_snd
  exact ((bulkHamiltonian_continuous (n+1) M f v).comp hp).measurable

lemma twoFreshMarkedTest_measurable (n M r : ℕ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Measurable (fun p : TwoFreshDisorder (n+1) M × (Fin r → NormalizedSpin (n+1)) =>
      bulkMarkedTest (n+1) r F Ψ Φ p.1.2 p.2) := by
  have hp : Continuous (fun p : TwoFreshDisorder (n+1) M × (Fin r → NormalizedSpin (n+1)) =>
      (p.1.2,p.2)) := continuous_fst.snd.prodMk continuous_snd
  exact ((bulkMarkedTest_continuous (n+1) r F Ψ Φ).comp hp).measurable

lemma bulkFreshNumerator_measurable (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Measurable (bulkFreshNumerator n M r f v F Ψ Φ) := by
  let H := fun (p : TwoFreshDisorder (n+1) M) (x : NormalizedSpin (n+1)) =>
    bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x
  let G := fun (p : TwoFreshDisorder (n+1) M) (x : Fin r → NormalizedSpin (n+1)) =>
    bulkMarkedTest (n+1) r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) p.2 x
  change Measurable (fun p => gibbsReplicaMean (unitSphereLaw (n+1)) (H p) r (G p))
  exact kernel_replicaMean_measurable (Kernel.const (TwoFreshDisorder (n+1) M) (unitSphereLaw (n+1)))
    (H:=H) (G:=G) (twoFreshHamiltonian_measurable n M f v)
    (twoFreshMarkedTest_measurable n M r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0))

lemma bulkFreshDenominator_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) :
    Measurable (bulkFreshDenominator n M f v) := by
  apply kernel_tiltMean_measurable (Kernel.const (TwoFreshDisorder (n+1) M) (unitSphereLaw (n+1)))
    (H:=fun p x => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x)
    (twoFreshHamiltonian_measurable n M f v)
  change Measurable (fun p : TwoFreshDisorder (n+1) M × NormalizedSpin (n+1) =>
    Real.exp (f (inner ℝ p.2.val p.1.2.1)+f (inner ℝ p.2.val p.1.2.2)))
  exact (((f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd.fst)).add
    (f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd.snd))).exp)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRestorationLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma bulkFresh_exact_restoration (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (a : BulkDisorder (n+1) (M+2)) :
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+2) f v a.1 a.2) r
      (bulkMarkedTest (n+1) r F Ψ Φ (bulkSeparateTwo (n+1) M a).2) =
      bulkFreshNumerator n M r f v F Ψ Φ (bulkSeparateTwo (n+1) M a) /
        bulkFreshDenominator n M f v (bulkSeparateTwo (n+1) M a)^r := by
  rw [bulk_replica_restore_two]
  congr 1
  apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f v (bulkSeparateTwo (n+1) M a).1.1 (bulkSeparateTwo (n+1) M a).1.2) r)
  funext x
  have h := restorationReplicaTest_twoMarks f F Ψ Φ (bulkSeparateTwo (n+1) M a).2.1
      (bulkSeparateTwo (n+1) M a).2.2 0 x
  simp only [restorationReplicaTest,restorationBlockTest,mul_assoc,bulkMarkedTest] at h ⊢
  convert h using 1
  all_goals try with_reducible_and_instances rfl

lemma bulkFresh_annealed_restoration (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    (∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+2) f v a.1 a.2) r
      (bulkMarkedTest (n+1) r F Ψ Φ (bulkSeparateTwo (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+2)) =
      ∫ p, bulkFreshNumerator n M r f v F Ψ Φ p / bulkFreshDenominator n M f v p^r
        ∂twoFreshDisorderLaw (n+1) M := by
  simp_rw [bulkFresh_exact_restoration]
  have hp := bulkSeparateTwo_preserving (n+1) M
  let g : TwoFreshDisorder (n+1) M → ℝ := fun p =>
    bulkFreshNumerator n M r f v F Ψ Φ p / bulkFreshDenominator n M f v p^r
  have hg : AEStronglyMeasurable g (twoFreshDisorderLaw (n+1) M) :=
    (((bulkFreshNumerator_measurable n M r f v F Ψ Φ).div
      ((bulkFreshDenominator_measurable n M f v).pow_const r)).aestronglyMeasurable)
  change (∫ a, g (bulkSeparateTwo (n+1) M a) ∂bulkDisorderLaw (n+1) (M+2)) =
    ∫ p, g p ∂twoFreshDisorderLaw (n+1) M
  have hg' : AEStronglyMeasurable g
      ((bulkDisorderLaw (n+1) (M+2)).map (bulkSeparateTwo (n+1) M)) := by
    rw [hp.map_eq]
    exact hg
  have he := integral_map hp.measurable.aemeasurable hg'
  exact he.symm.trans (by rw [hp.map_eq]; rfl)

lemma bulkReplicaMean_sum (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {ι : Type*} (s : Finset ι)
    (G : ι→BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : ∀ i∈s,Measurable (Function.uncurry (G i)))
    (D : ι→ℝ) (hD : ∀ i∈s,0≤D i) (hb : ∀ i∈s,∀ a x,|G i a x|≤D i) :
    bulkReplicaMean n M f v r (fun a x => ∑ i∈s,G i a x)=
      ∑ i∈s,bulkReplicaMean n M f v r (G i) := by
  unfold bulkReplicaMean
  have hH : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) M => bulkHamiltonian (n+1) M f v a.1 a.2)) :=
    (bulkHamiltonian_continuous (n+1) M f v).measurable
  have he (a : BulkDisorder (n+1) M) :
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r
        (fun x => ∑ i∈s,G i a x)=
      ∑ i∈s,gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G i a) :=
    gibbsReplicaMean_sum_of_integrable (unitSphereLaw (n+1)) s
      (show Measurable (fun x => bulkHamiltonian (n+1) M f v a.1 a.2 x) from hH.of_uncurry_left)
      (bulkHamiltonian_exp_integrable n M f v a) (fun i hi => (hG i hi).of_uncurry_left)
      (fun i hi x => hb i hi a x)
  simp_rw [he]
  exact integral_finsetSum s fun i hi => kernel_replicaMean_bounded_integrable (bulkSpinKernel n M)
    (bulkDisorderLaw (n+1) M) hH (hG i hi) (hD i hi) (hb i hi)

lemma bulkReplicaMean_const_mul (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ) (c : ℝ) :
    bulkReplicaMean n M f v r (fun a x => c*G a x)=c*bulkReplicaMean n M f v r G := by
  unfold bulkReplicaMean
  simp_rw [replicaMean_const_mul]
  exact integral_const_mul _ _

lemma bulkReplicaMean_bound (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) {C : ℝ} (_hC : 0≤C) (hb : ∀ a x,|G a x|≤C) :
    |bulkReplicaMean n M f v r G|≤C := by
  have hb' : ∀ᵐ a ∂bulkDisorderLaw (n+1) M,
      ‖gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G a)‖≤C := by
    refine ae_of_all _ fun a => ?_
    rw [Real.norm_eq_abs]
    exact gibbsReplicaMean_bound_of_integrable (unitSphereLaw (n+1))
      ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
      hG.of_uncurry_left (bulkHamiltonian_exp_integrable n M f v a) (hb a)
  simpa [bulkReplicaMean] using
    norm_integral_le_of_norm_le_const hb'

lemma bulk_two_row_exchange (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T U : (Fin r→ℝ)→ℝ) (hT : Measurable T) (hU : Measurable U)
    (i j k l : Fin M) (hij : i≠j) (hkl : k≠l) :
    bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields i a x)*U (bulkPatternFields j a x))=
      bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields k a x)*U (bulkPatternFields l a x)) := by
  classical
  let p : Bool→Fin M := fun b => if b then k else l
  let q : Bool→Fin M := fun b => if b then i else j
  have hp : Function.Injective p := by
    intro b c h
    cases b <;> cases c <;> simp_all [p,Ne.symm hkl]
  have hq : Function.Injective q := by
    intro b c h
    cases b <;> cases c <;> simp_all [q,Ne.symm hij]
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair p q hp hq
  have hek : e k=i := by simpa [p,q] using he true
  have hel : e l=j := by simpa [p,q] using he false
  have hm : Measurable (Function.uncurry (fun a x => G x*T (bulkPatternFields k a x)*U (bulkPatternFields l a x))) :=
    ((hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _))).mul
      (hU.comp (bulkPatternFields_measurable _ _ _ _))
  have ht := bulkReplicaMean_permute n M f v r e _ hm
  change bulkReplicaMean n M f v r (fun a x =>
    G x*T (fun i => ∑ t,a.1 (e k) t*(x i).val t)*U (fun i => ∑ t,a.1 (e l) t*(x i).val t))=_ at ht
  rw [hek,hel] at ht
  exact ht

lemma bulk_pattern_sum_first (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T : (Fin r→ℝ)→ℝ) (hT : Measurable T)
    {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (hGC : ∀ x,|G x|≤C) (hTD : ∀ z,|T z|≤D)
    (j : Fin M) :
    bulkReplicaMean n M f v r (fun a x => G x*∑ i,T (bulkPatternFields i a x))=
      M*bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields j a x)) := by
  simp_rw [Finset.mul_sum]
  rw [bulkReplicaMean_sum n M r f v Finset.univ _
    (fun i _ => (hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _)))
    (fun _=>C*D) (fun _ _ => mul_nonneg hC hD)
    (fun _ _ a x => by simpa only [abs_mul] using mul_le_mul (hGC x) (hTD _) (abs_nonneg _) hC)]
  simp_rw [bulk_row_exchange n M f v r G hG T hT _ j]
  simp

lemma bulk_pattern_sum_second (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T : (Fin r→ℝ)→ℝ) (hT : Measurable T)
    {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (hGC : ∀ x,|G x|≤C) (hTD : ∀ z,|T z|≤D)
    (k l : Fin M) (hkl : k≠l) :
    bulkReplicaMean n M f v r (fun a x => G x*(∑ i,T (bulkPatternFields i a x))^2)=
      M*bulkReplicaMean n M f v r (fun a x => G x*(T (bulkPatternFields k a x))^2)+
      M*((M:ℝ)-1)*bulkReplicaMean n M f v r
        (fun a x => G x*T (bulkPatternFields k a x)*T (bulkPatternFields l a x)) := by
  classical
  let W := fun i j (a : BulkDisorder (n+1) M) (x : Fin r→NormalizedSpin (n+1)) =>
    G x*T (bulkPatternFields i a x)*T (bulkPatternFields j a x)
  have hm (i j) : Measurable (Function.uncurry (W i j)) :=
    ((hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _))).mul
      (hT.comp (bulkPatternFields_measurable _ _ _ _))
  have hb (i j) (a : BulkDisorder (n+1) M) (x : Fin r→NormalizedSpin (n+1)) :
      |W i j a x|≤C*D*D := by
    dsimp [W]; rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hGC x) (hTD _) (abs_nonneg _) hC)
      (hTD _) (abs_nonneg _) (mul_nonneg hC hD)
  have hf : (fun a x => G x*(∑ i,T (bulkPatternFields i a x))^2)=
      (fun a x => ∑ i : Fin M,∑ j : Fin M,W i j a x) := by
    funext a x
    simp only [sq,Finset.sum_mul,Finset.mul_sum,W,mul_assoc]
    rw [Finset.sum_comm]
  rw [hf]
  rw [bulkReplicaMean_sum n M r f v Finset.univ (fun i a x => ∑ j,W i j a x)
    (fun i _ => Finset.measurable_sum _ fun j _ => hm i j)
    (fun _ => M*(C*D*D)) (fun _ _ => by positivity)
    (fun i _ a x => (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j _ => hb i j a x).trans_eq (by simp)))]
  simp_rw [bulkReplicaMean_sum n M r f v Finset.univ (W _)
    (fun j _ => hm _ j) (fun _=>C*D*D) (fun _ _ => by positivity) (fun j _ a x => hb _ j a x)]
  let d := bulkReplicaMean n M f v r (fun a x => G x*(T (bulkPatternFields k a x))^2)
  let o := bulkReplicaMean n M f v r (W k l)
  have he (i j : Fin M) : bulkReplicaMean n M f v r (W i j)=
      o+if i=j then d-o else 0 := by
    by_cases hij : i=j
    · subst j
      rw [ite_eq_left rfl]
      have h := bulk_row_exchange n M f v r G hG (fun z => (T z)^2) (hT.pow_const 2) i k
      dsimp [W]
      simp only [sq,mul_assoc] at h ⊢
      change _=o+(d-o)
      rw [show o+(d-o)=d by ring]
      simpa only [d,sq,mul_assoc] using h
    · rw [ite_eq_right hij,add_zero]
      exact bulk_two_row_exchange n M f v r G hG T T hT hT i j k l hij hkl
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  dsimp [d,o,W]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma stepCumulative_pos {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) (i : Fin k) :
    0 < stepCumulative w i := by
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> first | exact (hw j).le | rfl
  · exact ⟨0,Finset.mem_univ _,by simpa only [ite_eq_left (Fin.zero_le _)] using hw 0⟩

lemma stepCumulative_lt_one {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : Fin k) :
    stepCumulative w i < 1 := by
  rw [← hw1]
  apply Finset.sum_lt_sum
  · intro j _
    split_ifs <;> first | rfl | exact (hw j).le
  · refine ⟨Fin.last k,Finset.mem_univ _,?_⟩
    have hnot : ¬Fin.last k ≤ i.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]
      omega
    simpa only [ite_eq_right hnot] using hw (Fin.last k)

lemma stepCumulative_strictMono {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) : StrictMono (stepCumulative w) := by
  intro i j hij
  apply Finset.sum_lt_sum
  · intro a _
    by_cases hai : a ≤ i.castSucc
    · have haj : a ≤ j.castSucc := hai.trans (Fin.castSucc_le_castSucc_iff.mpr hij.le)
      simp only [ite_eq_left hai,ite_eq_left haj,le_refl]
    · simp only [ite_eq_right hai]
      split_ifs <;> first | exact (hw a).le | rfl
  · refine ⟨j.castSucc,Finset.mem_univ _,?_⟩
    have hnot : ¬j.castSucc ≤ i.castSucc := by simpa only [Fin.castSucc_le_castSucc_iff] using not_le.mpr hij
    simpa only [ite_eq_right hnot,ite_eq_left le_rfl] using hw j.castSucc

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldRounding
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma sub_roundLower_lt (N : ℕ) {x : ℝ} (_hx : 0 ≤ x) : x-roundLower N x < 1/(N+1:ℕ) := by
  have h := Nat.lt_floor_add_one ((N+1:ℕ)*x)
  unfold roundLower
  rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ (by positivity : (0:ℝ)<(N+1:ℕ))]
  simpa only [mul_comm,add_comm] using h

lemma roundLower_measurable (N : ℕ) : Measurable (roundLower N) := (roundLower_monotone N).measurable

lemma BoundedField.round_error {H : ℝ} (f : BoundedField H) (N : ℕ) (u : Time) :
    |f.round N u-f u| ≤ 1/(N+1:ℕ) := by
  change |roundLower N (f u)-f u| ≤ _
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (roundLower_le N (f.nonneg u)))]
  exact (sub_roundLower_lt N (f.nonneg u)).le

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_CompactArrayMap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

lemma compactMapBlock_continuous {e : K→L} (he : Continuous e) (n : ℕ) :
    Continuous (compactMapBlock e n) := by
  unfold compactMapBlock
  fun_prop


variable [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
  [SecondCountableTopology K] [SecondCountableTopology L]

lemma compactMapLaw_integral (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K))
    (F : CompactArray L→ℝ) (hF : Measurable F) :
    (∫ Q, F Q ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
      ∫ Q, F (compactMapArray e Q) ∂(μ : Measure (CompactArray K)) :=
  integral_map (compactMapArray_continuous he).measurable.aemeasurable hF.aestronglyMeasurable

lemma compactMapLaw_gg (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ),
      compactGGDefect μ n i f g=0) (n : ℕ) (i : Fin n)
    (f : CompactBlock L n →ᵇ ℝ) (g : L →ᵇ ℝ) :
    compactGGDefect (compactMapLaw e he μ) n i f g=0 := by
  let f' := f.compContinuous ⟨compactMapBlock e n,compactMapBlock_continuous he n⟩
  let g' := g.compContinuous ⟨e,he⟩
  have hmul (a b : ℕ) :
      (∫ Q, f (compactBlock n Q)*g (Q a b) ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
        ∫ Q, f' (compactBlock n Q)*g' (Q a b) ∂(μ : Measure (CompactArray K)) := by
    exact compactMapLaw_integral e he μ _
      ((f.measurable.comp (compactBlock_continuous n).measurable).mul (g.measurable.comp (by fun_prop)))
  have hf : (∫ Q, f (compactBlock n Q) ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
      ∫ Q, f' (compactBlock n Q) ∂(μ : Measure (CompactArray K)) := by
    exact compactMapLaw_integral e he μ _
      (f.measurable.comp (compactBlock_continuous n).measurable)
  have hg : (∫ Q, g (Q 0 1) ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
      ∫ Q, g' (Q 0 1) ∂(μ : Measure (CompactArray K)) := by
    exact compactMapLaw_integral e he μ _ (by fun_prop)
  unfold compactGGDefect
  simp_rw [hmul,hf,hg]
  exact hGG n i f' g'

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma indexedCommonDepth_ultrametric (n : ℕ) (a b c : IndexedLeaf n) :
    min (indexedCommonDepth n a b) (indexedCommonDepth n a c)≤ indexedCommonDepth n b c := by
  let l := min (indexedCommonDepth n a b) (indexedCommonDepth n a c)
  apply (indexedLeafSharedVertex_eq_iff n b c l).mp
  exact ((indexedLeafSharedVertex_eq_iff n a b l).mpr (min_le_left _ _)).symm.trans
    ((indexedLeafSharedVertex_eq_iff n a c l).mpr (min_le_right _ _))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_GibbsArrayGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
section
variable {A S K : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [CompactSpace K]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))
variable (Q : S → S → K) (hQ : Measurable (Function.uncurry Q))

omit [CompactSpace K] in
lemma gibbsOverlapArray_closed_full {F : Set (CompactArray K)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→S, overlapArray Q x ∈ F) :
    gibbsOverlapArrayLaw κ P H hH Q hQ F=1 := by
  have hp : (fun a : A×(ℕ→S) => overlapArray Q a.2) ⁻¹' F=univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (fun a : A×(ℕ→S) => overlapArray Q a.2) _) F=1
  have hm : Measurable (fun a : A×(ℕ→S) => overlapArray Q a.2) :=
    (overlapArray_measurable Q hQ).comp measurable_snd
  rw [Measure.map_apply hm hF.measurableSet,hp]
  exact measure_univ
end

lemma compactMapLaw_exchangeable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
    [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
    [SecondCountableTopology K] [SecondCountableTopology L]
    (f : K→L) (hf : Continuous f) (μ : ProbabilityMeasure (CompactArray K))
    (e : Equiv.Perm ℕ)
    (he : MeasurePreserving (compactRelabel (K:=K) e) (μ : Measure _) (μ : Measure _)) :
    MeasurePreserving (compactRelabel (K:=L) e) (compactMapLaw f hf μ : Measure _)
      (compactMapLaw f hf μ : Measure _) := by
  refine ⟨(compactRelabel_continuous e).measurable,?_⟩
  change Measure.map _ (Measure.map (compactMapArray f) _) = _
  rw [Measure.map_map (compactRelabel_continuous e).measurable (compactMapArray_continuous hf).measurable]
  change Measure.map (compactMapArray f ∘ compactRelabel e) _ = _
  rw [← Measure.map_map (compactMapArray_continuous hf).measurable he.measurable,he.map_eq]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkLimitGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

lemma bulkGibbsArray_closed_full (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {F : Set (CompactArray CompactOverlap)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→NormalizedSpin (n+1), overlapArray bulkOverlap x ∈ F) :
    bulkGibbsArrayLaw n M f v F=1 :=
  gibbsOverlapArray_closed_full _ _ _ _ _ _ hF hfull

lemma bulkGibbsArray_limit_diagonal (f : ℝ→ᵇℝ) (M : ℕ→ℕ) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactOverlap ∂(ν : Measure _), ∀ i, (Q i i).val=1 := by
  rw [ae_all_iff]
  intro i
  have hc : IsClosed {Q : CompactArray CompactOverlap | (Q i i).val=1} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc
    (fun n => bulkGibbsArray_closed_full (s n) (M (s n)) f (v (s n)) hc
      (fun x => spinOverlap_self (x i)))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedMarkedSelection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma strictRoundModel_strict {H : ℝ} (q : BoundedField H) (n : ℕ) :
    StrictMono (strictRoundModel q n).value :=
  (exists_finiteFieldModel_strict (q.round n) (q.round n).measurable (q.round_finite n)).choose_spec

lemma roundTimeValue_mono (q : BoundedField 1) (n : ℕ) : Monotone (roundTimeValue q n) :=
  (strictRoundModel q n).monotone_value

lemma BoundedField.round_tendsto {H : ℝ} (q : BoundedField H) (u : Time) :
    Tendsto (fun n => q.round n u) atTop (𝓝 (q u)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  simpa only [Real.dist_eq,Nat.cast_add,Nat.cast_one] using q.round_error n u

lemma roundTime_tendsto (q : Time→Time) (hq : Monotone q) (u : Time) :
    Tendsto (fun n => roundTime (unitQuantileField q hq) n u) atTop (𝓝 (q u)) :=
  tendsto_subtype_rng.mpr ((unitQuantileField q hq).round_tendsto u)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkEmpiricalLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

lemma bulk_density_factors (M s : ℕ→ℕ) (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2) atTop (𝓝 0) ∧
    Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)*((M (s n)+1:ℕ):ℝ)/(s n+1:ℕ)^2)
      atTop (𝓝 (α^2)) := by
  have hn : Tendsto (fun n => ((s n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hs)
  have hi : Tendsto (fun n => (((s n+1:ℕ):ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hfirst := hd.mul hi
  have hsecond := hd.mul (hd.sub hi)
  constructor
  · convert hfirst using 1 <;> try simp
    funext n
    field_simp
  · convert hsecond using 1 <;> try ring_nf
    funext n
    push_cast
    field_simp
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkPairLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkFiniteReplicaLaw_integral (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) {C : ℝ} (hb : ∀ a x,|G a x|≤C) :
    (∫ p,G p.1 p.2 ∂bulkFiniteReplicaLaw n M r f v)=bulkReplicaMean n M f v r G := by
  have hi : Integrable (Function.uncurry G) (bulkFiniteReplicaLaw n M r f v) :=
    Integrable.of_bound hG.aestronglyMeasurable C (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, Function.uncurry] using hb p.1 p.2)
  change (∫ p,Function.uncurry G p ∂bulkFiniteReplicaLaw n M r f v)=_
  rw [bulkFiniteReplicaLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact ae_of_all _ fun a => gibbsProbabilityKernel_replica_integral (bulkSpinKernel n M)
    (fun a => bulkHamiltonian (n+1) M f v a.1 a.2) (bulkHamiltonian_continuous _ _ _ _).measurable
    a (bulkHamiltonian_exp_integrable n M f v a) r (G a)

lemma bulkPairLaw_integral (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) (F : BulkPairRange K→ᵇℝ) :
    (∫ p,F p ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K)))=
      bulkReplicaMean n M f v 2 (fun a x => F (bulkCompactPair n M w K hK (a,x))) := by
  change (∫ p,F p ∂(bulkFiniteReplicaLaw n M 2 f v).map (bulkCompactPair n M w K hK))=_
  have he := integral_map (μ:=bulkFiniteReplicaLaw n M 2 f v)
    (bulkCompactPair_measurable n M w K hK).aemeasurable F.measurable.aestronglyMeasurable
  change (∫ p,F p ∂(bulkFiniteReplicaLaw n M 2 f v).map (bulkCompactPair n M w K hK))=
    (∫ p,F (bulkCompactPair n M w K hK p) ∂bulkFiniteReplicaLaw n M 2 f v) at he
  rw [he]
  exact bulkFiniteReplicaLaw_integral n M 2 f v
    (fun a x => F (bulkCompactPair n M w K hK (a,x)))
    (F.measurable.comp (bulkCompactPair_measurable n M w K hK))
    (fun a x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (bulkCompactPair n M w K hK (a,x)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_AnnealedMarkedReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace SphericalPerceptronFreeEnergy
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_marked_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : A→(Fin r→S)→ℝ}
    (hG : Measurable (Function.uncurry G)) {B : ℝ} (hGB : ∀ a x,|G a x|≤B) :
    (∫ a,G a.1 (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH)=
      ∫ a,gibbsReplicaMean (κ a) (H a) r (G a) ∂P := by
  let := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val)) :=
    hG.comp (measurable_fst.prodMk (by fun_prop))
  have hi : Integrable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using hGB a.1 (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  rw [kernelInfiniteReplica_prefix_integral _ a r hG.of_uncurry_left]
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r (G a)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

lemma bulkB_pairAverage (n M : ℕ) (f : Jet3) (a : BulkDisorder (n+1) M)
    (x : Fin 2→NormalizedSpin (n+1)) :
    bulkB (n+1) M f a.1 (x 0) (x 1)=bulkPairAverage n M f.d1 a x := by
  simp only [bulkB,bulkPairAverage,pairFieldMark,Fin.prod_univ_two,bulkPatternFields]

lemma bulkB_symm (N M : ℕ) (f : Jet3) (a : Fin M→Fin N→ℝ) (x y : NormalizedSpin N) :
    bulkB N M f a x y=bulkB N M f a y x := by
  unfold bulkB
  simp_rw [mul_comm (f.d1 _) (f.d1 _)]

lemma bulkMarkedArray_block (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :
    (∫ Q,F (compactBlock r Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=
      bulkReplicaMean n M f.f v r (fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j))) := by
  change (∫ Q,F (compactBlock r Q) ∂Measure.map (bulkMarkedArray n M f K hK)
    (annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
      (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)))=_
  have hm : Measurable (fun Q : CompactArray (BulkPairRange K) => F (compactBlock r Q)) :=
    F.measurable.comp (compactBlock_continuous r).measurable
  rw [integral_map (bulkMarkedArray_measurable n M f K hK).aemeasurable hm.aestronglyMeasurable]
  unfold bulkReplicaMean
  apply annealedInfiniteReplica_marked_prefix (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f.f v)) r
    (G := fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j)))
  · apply F.measurable.comp
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    have hm : Measurable (fun p : BulkDisorder (n+1) M×(Fin r→NormalizedSpin (n+1)) => (p.2 i,p.2 j)) := by fun_prop
    exact ((bulkOverlap_measurable _).comp hm).prodMk
      (((bulkB_measurable _ _ _).comp (measurable_fst.prodMk hm)).subtype_mk)
  · intro a x
    exact F.norm_coe_le_norm _

lemma bulkMarkedArray_exchangeable (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=BulkPairRange K) e)
      (bulkMarkedArrayLaw n M f v K hK : Measure _) (bulkMarkedArrayLaw n M f v K hK : Measure _) := by
  have hr := annealedInfiniteReplica_reindex (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v) e
  have hm := bulkMarkedArray_measurable n M f K hK
  refine ⟨(compactRelabel_continuous e).measurable,?_⟩
  change Measure.map _ (Measure.map (bulkMarkedArray n M f K hK) _)=_
  rw [Measure.map_map (compactRelabel_continuous e).measurable hm]
  change Measure.map ((bulkMarkedArray n M f K hK) ∘
    (fun a : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => (a.1,fun i => a.2 (e i)))) _=_
  rw [←Measure.map_map hm hr.measurable,hr.map_eq]
  rfl

lemma bulkMarkedArray_overlap (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    compactMapLaw Prod.fst continuous_fst (bulkMarkedArrayLaw n M f v K hK)=bulkGibbsArrayLaw n M f.f v := by
  apply Subtype.ext
  change Measure.map (fun Q : CompactArray (BulkPairRange K) => fun i j => (Q i j).1)
    (Measure.map (bulkMarkedArray n M f K hK) _) = _
  rw [Measure.map_map (by fun_prop) (bulkMarkedArray_measurable _ _ _ _ _)]
  rfl

lemma bulkMarkedArray_pair (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    (bulkMarkedArrayLaw n M f v K hK).map (f := fun Q => Q 1 0) (Measurable.aemeasurable (by fun_prop))=
      bulkPairLaw n M f.f f.d1 v K hK := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [ProbabilityMeasure.toMeasure_map,integral_map (by fun_prop : Measurable (fun Q : CompactArray (BulkPairRange K)=>Q 1 0)).aemeasurable F.continuous.aestronglyMeasurable,
    bulkPairLaw_integral]
  let T : CompactBlock (BulkPairRange K) 2→ᵇℝ := F.compContinuous ⟨fun Q=>Q 1 0,by fun_prop⟩
  have he := bulkMarkedArray_block n M f v K hK 2 T
  change (∫ Q : CompactArray (BulkPairRange K),F (Q 1 0) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=_ at he
  rw [he]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 2)
    funext x
    apply congrArg F
    change bulkMarkedEntry n M f K hK a (x 1) (x 0) = bulkCompactPair n M f.d1 K hK (a,x)
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (bulkB_symm _ _ _ _ _ _).trans (bulkB_pairAverage _ _ _ a x)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma singleFieldMark_measurable (w : ℝ→ᵇℝ) : Measurable (singleFieldMark w) := by
  unfold singleFieldMark; fun_prop
lemma singleFieldMark_bound (w : ℝ→ᵇℝ) (z : Fin 1→ℝ) : |singleFieldMark w z|≤‖w‖ := w.norm_coe_le_norm _

lemma bulkSingleAverage_measurable (n M : ℕ) (w : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (bulkSingleAverage n M w)) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ => (singleFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)

lemma bulkSingleAverage_bound (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 1→NormalizedSpin (n+1)) : |bulkSingleAverage n M w a x|≤M/(n+1:ℕ)*‖w‖ := by
  unfold bulkSingleAverage
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(((n+1:ℕ):ℝ)⁻¹))]
  have h : |∑ i : Fin M,singleFieldMark w (bulkPatternFields i a x)|≤M*‖w‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => singleFieldMark_bound w _).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

lemma bulk_marked_last_single (n M : ℕ) (f w w' : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+2) f v 1 (fun a x =>
      singleFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x)*
      singleFieldMark w' (bulkPatternFields (Fin.last (M+1)) a x))=
    ∫ p,bulkFreshNumerator n M 1 f v 1
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator n M f v p^1 ∂twoFreshDisorderLaw (n+1) M := by
  rw [←bulkFresh_annealed_restoration]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    apply congrArg (gibbsReplicaMean _ _ 1)
    funext x
    simp only [BoundedContinuousFunction.coe_one,Pi.one_apply,bulkMarkedTest,one_mul,gaussianMixedTest_apply,Fin.prod_univ_one,
      singleFieldMark]
    rfl

lemma bulkSingleAverage_first (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+2) f v 1 (bulkSingleAverage n (M+2) w)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)*(∫ p,bulkFreshNumerator n M 1 f v 1
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
      bulkFreshDenominator n M f v p^1 ∂twoFreshDisorderLaw (n+1) M) := by
  unfold bulkSingleAverage
  rw [bulkReplicaMean_const_mul]
  have h := bulk_pattern_sum_first n (M+2) 1 f v (fun _=>1) measurable_const
    _ (singleFieldMark_measurable w) (by norm_num : (0:ℝ)≤1) (norm_nonneg w)
    (fun _=>by norm_num) (singleFieldMark_bound w) ((Fin.last M).castSucc)
  simp only [one_mul] at h
  rw [h,←bulk_marked_last_single n M f w 1 v]
  simp only [singleFieldMark,BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one]
  ring

lemma bulkSingleAverage_second (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+2) f v 1 (fun a x => (bulkSingleAverage n (M+2) w a x)^2)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)^2*
      bulkReplicaMean n (M+2) f v 1 (fun a x =>
        (singleFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)+
    (((M+2:ℕ):ℝ)*((M+1:ℕ):ℝ)/(n+1:ℕ)^2)*(∫ p,bulkFreshNumerator n M 1 f v 1
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
      bulkFreshDenominator n M f v p^1 ∂twoFreshDisorderLaw (n+1) M) := by
  have hf : (fun a x => (bulkSingleAverage n (M+2) w a x)^2)=
      (fun a x => (((n+1:ℕ):ℝ)⁻¹)^2*((∑ i,singleFieldMark w (bulkPatternFields i a x))^2)) := by
    funext a x; unfold bulkSingleAverage; ring
  have hkl : (Fin.last M).castSucc≠Fin.last (M+1) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at this
    omega
  rw [hf,bulkReplicaMean_const_mul]
  have h := bulk_pattern_sum_second n (M+2) 1 f v (fun _=>1) measurable_const
    _ (singleFieldMark_measurable w) (by norm_num : (0:ℝ)≤1) (norm_nonneg w)
    (fun _=>by norm_num) (singleFieldMark_bound w) _ _ hkl
  simp only [one_mul] at h
  rw [h,bulk_marked_last_single]
  simp only [div_eq_mul_inv,inv_pow]
  push_cast
  ring

lemma bulkSingleAverage_diagonal_bound (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    |bulkReplicaMean n (M+2) f v 1 (fun a x =>
        (singleFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)|≤‖w‖^2 := by
  apply bulkReplicaMean_bound _ _ _ _ _ _
    (((singleFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)).pow_const 2) (by positivity)
  intro a x
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (singleFieldMark_bound w _) 2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleEmpiricalLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

lemma bulkSingleAverage_first_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (α c : ℝ) (w : ℝ→ᵇℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 c)) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
      (bulkSingleAverage (s n) (M (s n)+2) w)) atTop (𝓝 (α*c)) := by
  simp_rw [bulkSingleAverage_first]
  exact hd.mul ht

lemma bulkSingleAverage_second_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α c : ℝ) (w : ℝ→ᵇℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 (c^2))) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
      (fun a x => (bulkSingleAverage (s n) (M (s n)+2) w a x)^2)) atTop (𝓝 ((α*c)^2)) := by
  have hfac := bulk_density_factors M s hs α hd
  have herr : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2*
      bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1 (fun a x =>
        (singleFieldMark w (bulkPatternFields ((Fin.last (M (s n))).castSucc) a x))^2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [zero_mul] using hfac.1.mul_const (‖w‖^2))
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2)]
    exact mul_le_mul_of_nonneg_left (bulkSingleAverage_diagonal_bound (s n) (M (s n)) g.f w (v (s n))) (by positivity)
  simp_rw [bulkSingleAverage_second]
  simpa only [zero_add,mul_pow] using herr.add (hfac.2.mul ht)

theorem bulk_single_empirical_limits (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (bulkSingleAverage (s n) (M (s n)+2) w)) atTop (𝓝 (α*c)) ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkSingleAverage (s n) (M (s n)+2) w a x)^2)) atTop (𝓝 ((α*c)^2)) := by
  obtain ⟨c,hc,ht⟩ := bulk_single_limit_exists M g v s hlim hGG hgeo hn w
  refine ⟨c,hc,?_,?_⟩
  · apply bulkSingleAverage_first_limit M g v s α c w hd
    simpa [secondPairMark,pairMarkPower] using ht false
  · apply bulkSingleAverage_second_limit M g v s hs α c w hd
    simpa [secondPairMark,pairMarkPower] using ht true

lemma bulkReplicaMean_annealed (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hb : ∀ a x,|G a x|≤C) :
    bulkReplicaMean n M f v r G =
      ∫ p,G p.1 (fun i => p.2 i.val) ∂bulkAnnealedReplicaLaw n M f v := by
  symm
  exact annealedInfiniteReplica_marked_prefix (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f v) (bulkGibbsHamiltonian_measurable n M f v)
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f v)) r hG hb

lemma bulkReplicaPrefix_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hb : ∀ a x,|G a x|≤C) :
    Integrable (fun p => G p.1 (fun i => p.2 i.val)) (bulkAnnealedReplicaLaw n M f v) := by
  have hm : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => G p.1 (fun i => p.2 i.val)) :=
    hG.comp (measurable_fst.prodMk (Measurable.of_eval fun coordinate =>
      (measurable_pi_apply coordinate.val).comp measurable_snd))
  apply Integrable.of_bound hm.aestronglyMeasurable C
  exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p.1 (fun i => p.2 i.val)

lemma bulkReplicaMean_centered_square (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hC : 0≤C) (hb : ∀ a x,|G a x|≤C) (c : ℝ) :
    bulkReplicaMean n M f v r (fun a x => (G a x-c)^2)=
      bulkReplicaMean n M f v r (fun a x => (G a x)^2)-2*c*bulkReplicaMean n M f v r G+c^2 := by
  have hsq : ∀ a x,|(G a x)^2|≤C^2 := fun a x => by
    rw [abs_pow]; exact (sq_le_sq₀ (abs_nonneg _) hC).mpr (hb a x)
  have hcent : ∀ a x,|(G a x-c)^2|≤(C+|c|)^2 := fun a x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub (G a x) c).trans (add_le_add (hb a x) le_rfl)) 2
  rw [bulkReplicaMean_annealed _ _ _ _ _ _ ((hG.sub_const c).pow_const 2) _ hcent,
    bulkReplicaMean_annealed _ _ _ _ _ _ (hG.pow_const 2) _ hsq,
    bulkReplicaMean_annealed _ _ _ _ _ _ hG _ hb]
  have hg := bulkReplicaPrefix_integrable n M f v r G hG C hb
  have hg2 := bulkReplicaPrefix_integrable n M f v r (fun a x => (G a x)^2) (hG.pow_const 2) (C^2) hsq
  simp_rw [sub_sq]
  have h₁ : Integrable (fun p => (G p.1 (fun i => p.2 i.val))^2-2*G p.1 (fun i => p.2 i.val)*c)
      (bulkAnnealedReplicaLaw n M f v) := hg2.sub ((hg.const_mul 2).mul_const c)
  have h₂ : Integrable (fun p => 2*G p.1 (fun i => p.2 i.val)*c)
      (bulkAnnealedReplicaLaw n M f v) := (hg.const_mul 2).mul_const c
  rw [integral_add h₁ (integrable_const (μ:=bulkAnnealedReplicaLaw n M f v) (c^2)),
    integral_sub hg2 h₂,integral_mul_const,integral_const_mul]
  simp
  ring

theorem bulk_single_L2_concentration (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkSingleAverage (s n) (M (s n)+2) w a x-α*c)^2)) atTop (𝓝 0) := by
  obtain ⟨c,hc,h1,h2⟩ := bulk_single_empirical_limits M g v s hs α hd hlim hGG hgeo hn w
  refine ⟨c,hc,?_⟩
  have he n := bulkReplicaMean_centered_square (s n) (M (s n)+2) g.f (v (s n)) 1
    (bulkSingleAverage (s n) (M (s n)+2) w) (bulkSingleAverage_measurable _ _ _) _
    (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖w‖)
    (bulkSingleAverage_bound _ _ _) (α*c)
  simp_rw [he]
  convert (h2.sub (h1.const_mul (2*(α*c)))).add_const ((α*c)^2) using 1
  all_goals try with_reducible_and_instances rfl
  ring_nf

theorem bulk_diagonal_C_concentration (M : ℕ→ℕ) (g : Jet3)
    (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val) :
    (∃ d : ℝ, |d|≤|α| * ‖g.d1‖^2 ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkB (s n+1) (M (s n)+2) g a.1 (x 0) (x 0)-d)^2)) atTop (𝓝 0)) ∧
    (∃ c : ℝ, |c|≤|α| * ‖g.dilationMark hg‖ ∧
      Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 1
        (fun a x => (bulkC (s n+1) (M (s n)+2) g a.1 (x 0)-c)^2)) atTop (𝓝 0)) := by
  constructor
  · obtain ⟨c,hc,ht⟩ := bulk_single_L2_concentration M g v s hs α hd hlim hGG hgeo hn (g.d1*g.d1)
    refine ⟨α*c,?_,?_⟩
    · rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hc.trans (norm_mul_le _ _)) (abs_nonneg α)).trans_eq (by ring)
    · exact ht
  · obtain ⟨c,hc,ht⟩ := bulk_single_L2_concentration M g v s hs α hd hlim hGG hgeo hn (g.dilationMark hg)
    refine ⟨α*c,?_,?_⟩
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hc (abs_nonneg α)
    · exact ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedTangentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology BoundedContinuousFunction ContDiff

lemma exists_nat_perm_pair (i j : ℕ) (hij : i≠j) :
    ∃ e : Equiv.Perm ℕ,e 1=i ∧ e 0=j := by
  classical
  let u := Equiv.swap 1 i
  have hu : u 0≠i := by
    intro h
    have he : u 0=u 1 := by simpa [u] using h
    have := u.injective he
    omega
  refine ⟨u.trans (Equiv.swap (u 0) j),?_,?_⟩
  · change Equiv.swap (u 0) j (u 1)=i
    simp only [u,Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hu.symm hij
  · change Equiv.swap (u 0) j (u 0)=j
    exact Equiv.swap_apply_left _ _

lemma compact_exchangeable_offdiag_ae {K : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=K) e) (μ : Measure _) (μ : Measure _))
    (P : K→Prop) (hP : ∀ᵐ Q ∂(μ : Measure (CompactArray K)),P (Q 1 0)) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray K)),∀ i j,i≠j→P (Q i j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i=j
  · exact ae_of_all _ fun Q h => (h hij).elim
  · obtain ⟨e,he1,he0⟩ := exists_nat_perm_pair i j hij
    have h := (he e).quasiMeasurePreserving.ae hP
    simpa only [compactRelabel,he1,he0] using h.mono (fun Q h _ => h)

lemma bulkMarkedArray_limit_overlap (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (K : ℝ) (hK : ∀ n,(M (s n):ℝ)/(s n+1:ℕ)*‖f.d1‖^2≤K)
    {μ : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f.f (v (s n))) atTop
      (𝓝 (compactMapLaw Prod.fst continuous_fst μ)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (compactMapArray_continuous (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst))
  change Tendsto (fun n => compactMapLaw Prod.fst continuous_fst (bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n))) atTop (𝓝 (compactMapLaw Prod.fst continuous_fst μ)) at ht
  simpa only [bulkMarkedArray_overlap] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedTangentCanonical
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff NNReal

lemma nonnegativeSpinTime_val {q : CompactOverlap} (hq : 0≤q.val) :
    (nonnegativeSpinTime q).val=q.val := max_eq_left hq

lemma markedTimeLaw_factor (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    markedTimeLaw K μ=compactMapLaw nonnegativeSpinTime nonnegativeSpinTime_continuous
      (compactMapLaw Prod.fst continuous_fst μ) := by
  apply Subtype.ext
  change Measure.map _ (μ : Measure (CompactArray (BulkPairRange K)))=
    Measure.map _ (Measure.map _ (μ : Measure (CompactArray (BulkPairRange K))))
  rw [Measure.map_map (compactMapArray_continuous nonnegativeSpinTime_continuous).measurable
    (compactMapArray_continuous continuous_fst).measurable]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedSelfConsistency
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

lemma marked_overlap_geometry (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=BulkPairRange K) e) (μ : Measure _) (μ : Measure _))
    (hg : ∀ᵐ Q ∂(bulkJointLaw (compactMapLaw Prod.fst continuous_fst μ) : Measure (CompactArray CompactJointOverlap)),CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw (compactMapLaw Prod.fst continuous_fst μ) : Measure (CompactArray CompactJointOverlap)),0≤(Q 0 1).1.val) :
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).1=(Q j i).1) ∧
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j k,min (Q i j).1.val (Q i k).1.val≤(Q j k).1.val) ∧
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,0≤(Q i j).1.val) := by
  have h1 := ae_of_ae_map (compactMapArray_continuous bulkJointEmbedding_continuous).measurable.aemeasurable hg
  have h2 := ae_of_ae_map (compactMapArray_continuous (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable h1
  have h3 := ae_of_ae_map (compactMapArray_continuous bulkJointEmbedding_continuous).measurable.aemeasurable hn
  have h4 := ae_of_ae_map (compactMapArray_continuous (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable h3
  have hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).1=(Q j i).1 :=
    h2.mono fun Q hQ i j=>Subtype.ext (hQ.1 i j)
  refine ⟨hsy,h2.mono (fun Q hQ=>hQ.2.2),?_⟩
  have h10 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),0≤(Q 1 0).1.val := by
    filter_upwards [hsy,h4] with Q hQ hN
    change 0≤(Q 0 1).1.val at hN
    simpa only [hQ 1 0] using hN
  have ha := compact_exchangeable_offdiag_ae μ he (fun p=>0≤p.1.val) h10
  filter_upwards [ha,h2] with Q hQ hG
  intro i j
  by_cases hij : i=j
  · subst j
    have hd : (Q i i).1.val=1 := hG.2.1 i
    rw [hd]; norm_num
  · exact hQ i j hij

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkTimeLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma markedTimeLaw_geometry {K : ℝ} (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hs : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, (Q i j).1 = (Q j i).1)
    (hd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).1.val = 1)
    (hu : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j l,
      min (Q i j).1.val (Q i l).1.val ≤ (Q j l).1.val) :
    ∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l := by
  let e : BulkPairRange K → Time := fun p => nonnegativeSpinTime p.1
  have hc : Continuous e := nonnegativeSpinTime_continuous.comp continuous_fst
  have hmeas : MeasurableSet {Q : CompactArray Time |
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l} := by
    simp only [Set.ofPred_and,Set.ofPred_forall]
    exact (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter
      ((MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun l =>
        measurableSet_le (by fun_prop) (by fun_prop)))
  exact (ae_map_iff (compactMapArray_continuous hc).measurable.aemeasurable hmeas).mpr (by
  filter_upwards [hs,hd,hu] with Q hS hD hU
  refine ⟨fun i j => congrArg nonnegativeSpinTime (hS i j),?_,?_⟩
  · intro i
    apply Subtype.ext
    change max (Q i i).1.val 0 = 1
    rw [hD i]; norm_num
  · intro i j l
    change min (max (Q i j).1.val 0) (max (Q i l).1.val 0) ≤ max (Q j l).1.val 0
    rw [←max_min_distrib_right]
    exact max_le_max (hU i j l) le_rfl)

theorem bulk_marked_time_inputs (M : ℕ → ℕ) (g : Jet3) (v : ℕ → ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1 ≤ v n p)
    (hd : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ → ℕ) (hs : StrictMono s) (K : ℝ)
    (hK : ∀ n, (M (s n) : ℝ) / (s n+1 : ℕ) * ‖g.d1‖^2 ≤ K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    (∀ n (i : Fin n) (F : CompactBlock Time n →ᵇ ℝ) (a : Time →ᵇ ℝ),
      compactGGDefect (markedTimeLaw K μ) n i F a = 0) ∧
    (∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l) ∧
    (∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=Time) e)
      (markedTimeLaw K μ : Measure _) (markedTimeLaw K μ : Measure _)) := by
  have hp := bulkMarkedArray_limit_overlap M g v s K hK hlim
  have hgeom := bulk_limit_geometry M g.f v hv hd hs hp
  have hex e := compact_exchangeability_limit hlim e
    (fun n => bulkMarkedArray_exchangeable (s n) (M (s n)) g (v (s n)) K (hK n) e)
  have hmarked := marked_overlap_geometry K μ hex hgeom.1 hgeom.2.1
  refine ⟨?_,?_,?_⟩
  · rw [markedTimeLaw_factor]
    exact compactMapLaw_gg nonnegativeSpinTime nonnegativeSpinTime_continuous _
      (bulk_limit_gg M g.f v hv hd hs hp)
  · apply markedTimeLaw_geometry μ hmarked.1 _ hmarked.2.1
    exact ae_of_ae_map (compactMapArray_continuous (show Continuous
      (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable
      (bulkGibbsArray_limit_diagonal g.f M v s hp)
  · exact fun e => compactMapLaw_exchangeable _ _ μ e (hex e)



lemma bulkB_diagonal_nonneg (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x : NormalizedSpin N) : 0 ≤ bulkB N M f a x x := by
  unfold bulkB
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _index _ => mul_self_nonneg _)

lemma bulkB_add_diagonal_bound (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x y : NormalizedSpin N) :
    2 * bulkB N M f a x y ≤ bulkB N M f a x x + bulkB N M f a y y := by
  let u j := f.d1 (∑ i, a j i * x.val i)
  let v j := f.d1 (∑ i, a j i * y.val i)
  have h : ∑ j, (2 * (u j * v j)) ≤ ∑ j, (u j * u j + v j * v j) := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (u j - v j)]
  have hh := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ (N:ℝ)⁻¹)
  simpa only [Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_assoc,mul_left_comm,
    u,v,bulkB] using hh

lemma bulkMarkedArray_closed_full (n M : ℕ) (f : Jet3) (v : ℕ → ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2 ≤ K) {F : Set (CompactArray (BulkPairRange K))}
    (hF : IsClosed F)
    (hfull : ∀ a : BulkDisorder (n+1) M, ∀ x : ℕ → NormalizedSpin (n+1),
      bulkMarkedArray n M f K hK (a,x) ∈ F) :
    bulkMarkedArrayLaw n M f v K hK F = 1 := by
  have hp : bulkMarkedArray n M f K hK ⁻¹' F = univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.1 a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (bulkMarkedArray n M f K hK) _) F = 1
  rw [Measure.map_apply (bulkMarkedArray_measurable _ _ _ _ _) hF.measurableSet,hp]
  exact measure_univ

theorem bulkMarkedArray_limit_mark_geometry (M : ℕ → ℕ) (f : Jet3) (v : ℕ → ℕ → ℝ)
    (s : ℕ → ℕ) (K : ℝ) (hK : ∀ n, (M (s n):ℝ)/(s n+1:ℕ)*‖f.d1‖^2 ≤ K)
    {μ : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, 0 ≤ (Q i i).2.val) ∧
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j,
      2*(Q i j).2.val ≤ (Q i i).2.val + (Q j j).2.val) := by
  constructor
  · apply ae_all_iff.mpr
    intro i
    have hc : IsClosed {Q : CompactArray (BulkPairRange K) | 0 ≤ (Q i i).2.val} :=
      isClosed_le continuous_const (by fun_prop)
    apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
    have h := weak_limit_closed_full hlim hc (fun n => bulkMarkedArray_closed_full
      (s n) (M (s n)) f (v (s n)) K (hK n) hc
      (fun _disorder _spins => bulkB_diagonal_nonneg _ _ _ _ _))
    simp only [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,h,ENNReal.coe_one]
  · apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    have hc : IsClosed {Q : CompactArray (BulkPairRange K) |
      2*(Q i j).2.val ≤ (Q i i).2.val + (Q j j).2.val} := isClosed_le (by fun_prop) (by fun_prop)
    apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
    have h := weak_limit_closed_full hlim hc (fun n => bulkMarkedArray_closed_full
      (s n) (M (s n)) f (v (s n)) K (hK n) hc
      (fun _disorder _spins => bulkB_add_diagonal_bound _ _ _ _ _ _))
    simp only [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,h,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkDiagonalLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkMarkedArray_limit_diagonal_const (M : ℕ → ℕ) (g : Jet3) (v : ℕ → ℕ → ℝ)
    (s : ℕ → ℕ) (K : ℝ) (hK : ∀ n, (M (s n):ℝ)/(s n+1:ℕ)*‖g.d1‖^2 ≤ K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) g (v (s n)) K (hK n)) atTop (𝓝 μ))
    (d : ℝ) (hL2 : Tendsto (fun n => bulkReplicaMean (s n) (M (s n)) g.f (v (s n)) 1
      (fun a x => (bulkB (s n+1) (M (s n)) g a.1 (x 0) (x 0)-d)^2)) atTop (𝓝 0)) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).2.val = d := by
  let F : CompactBlock (BulkPairRange K) 1 →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun Q => ((Q 0 0).2.val-d)^2,by fun_prop⟩
  let G : CompactArray (BulkPairRange K) →ᵇ ℝ := F.compContinuous ⟨compactBlock 1,compactBlock_continuous 1⟩
  have hzero : (∫ Q, G Q ∂(μ : Measure (CompactArray (BulkPairRange K)))) = 0 := by
    have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).continuousAt.tendsto.comp hlim
    have hfn n : (∫ Q, G Q ∂(bulkMarkedArrayLaw (s n) (M (s n)) g (v (s n)) K (hK n) : Measure _)) =
      bulkReplicaMean (s n) (M (s n)) g.f (v (s n)) 1
        (fun a x => (bulkB (s n+1) (M (s n)) g a.1 (x 0) (x 0)-d)^2) :=
      bulkMarkedArray_block (s n) (M (s n)) g (v (s n)) K (hK n) 1 F
    exact tendsto_nhds_unique (by simpa only [Function.comp_def,hfn] using ht) hL2
  have hz : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), (Q 0 0).2.val = d := by
    have ha := (integral_eq_zero_iff_of_nonneg
      (fun Q => show 0 ≤ G Q from sq_nonneg _) (G.integrable _)).mp hzero
    filter_upwards [ha] with Q hQ
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hQ)
  apply ae_all_iff.mpr
  intro i
  have he := compact_exchangeability_limit hlim (Equiv.swap 0 i)
    (fun n => bulkMarkedArray_exchangeable (s n) (M (s n)) g (v (s n)) K (hK n) _)
  simpa only [compactRelabel,Equiv.swap_apply_left] using he.quasiMeasurePreserving.ae hz

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_ContinuousCavityProfile
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cappedA_monotone (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ} (hB : B < 1) :
    Monotone (cappedA μ B) :=
  monotone_of_hasDerivAt_nonneg (cappedA_hasDerivAt μ hB) (fun _ => sq_nonneg _)

lemma continuousCavityProfile_mono (μ : Measure Time) [IsProbabilityMeasure μ]
    {B K d : ℝ} (hB : B < 1) (hd0 : 0 ≤ d) (hdK : d ≤ K) :
    Monotone (fun r => (continuousCavityProfile μ B hd0 hdK r).2.val) := by
  exact monotone_const.min (monotone_const.max
    ((cappedA_monotone μ hB).comp (Subtype.mono_coe _)))

lemma continuousCavityProfile_nonneg (μ : Measure Time) (B : ℝ) {K d : ℝ}
    (hd0 : 0 ≤ d) (hdK : d ≤ K) (r : Time) :
    0 ≤ (continuousCavityProfile μ B hd0 hdK r).1.val ∧
    0 ≤ (continuousCavityProfile μ B hd0 hdK r).2.val :=
  ⟨r.prop.1,le_min hd0 (le_max_left _ _)⟩

lemma continuousCavityProfile_le_diagonal (μ : Measure Time) (B : ℝ) {K d : ℝ}
    (hd0 : 0 ≤ d) (hdK : d ≤ K) (r : Time) :
    (continuousCavityProfile μ B hd0 hdK r).1.val ≤ (cavityTrueDiagonal hd0 hdK).1.val ∧
    (continuousCavityProfile μ B hd0 hdK r).2.val ≤ (cavityTrueDiagonal hd0 hdK).2.val :=
  ⟨r.prop.2,min_le_left _ _⟩

lemma continuousCavityProfile_eq (μ : Measure Time) [IsProbabilityMeasure μ]
    {B K d : ℝ} (hd0 : 0 ≤ d) (hdK : d ≤ K)
    (hμ : ∀ᵐ r : Time ∂μ, r.val ≤ B) {r : Time} {a : ℝ}
    (hr : r.val ≤ B) (ha0 : 0 ≤ a) (had : a ≤ d)
    (ha : a = ∫ t in 0..r.val, (realTail μ t)⁻¹^2) :
    (continuousCavityProfile μ B hd0 hdK r).2.val = a := by
  change min d (max 0 (cappedA μ B r.val)) = a
  rw [cappedA_eq_integral μ hμ r.prop.1 hr,←ha,max_eq_right ha0,min_eq_right had]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProbabilityMaps
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction BigOperators NNReal

lemma probabilityMap_tendsto_of_ae_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure Ω) (F : ℕ → Ω → X) (G : Ω → X)
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hlim : ∀ᵐ ω ∂(μ : Measure Ω), Tendsto (fun n => F n ω) atTop (𝓝 (G ω))) :
    Tendsto (fun n => μ.map (hF n).aemeasurable) atTop (𝓝 (μ.map hG.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have he n : (∫ x, f x ∂(μ.map (hF n).aemeasurable : Measure X)) =
      ∫ ω, f (F n ω) ∂(μ : Measure Ω) :=
    integral_map (hF n).aemeasurable f.measurable.aestronglyMeasurable
  have hg : (∫ x, f x ∂(μ.map hG.aemeasurable : Measure X)) =
      ∫ ω, f (G ω) ∂(μ : Measure Ω) :=
    integral_map hG.aemeasurable f.measurable.aestronglyMeasurable
  simp_rw [he,hg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.measurable.comp (hF n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
  exact hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DepthLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

lemma indexedDepthLaw_geometry (k : ℕ) (z : Fin k → ℝ) :
    ∀ᵐ R ∂(indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))),
      (∀ i j, R i j = R j i) ∧ (∀ i, R i i = Fin.last k) ∧
        ∀ i j l, min (R i j) (R i l) ≤ R j l := by
  apply (ae_map_iff ((indexedDepthArray_measurable k).comp measurable_snd).aemeasurable
    (by measurability)).mpr
  exact ae_of_all _ fun a => ⟨fun i j => indexedCommonDepth_comm k _ _,
    fun i => indexedCommonDepth_self k _,fun i j l => indexedCommonDepth_ultrametric k _ _ _⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_SphericalPatternRadial
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma spherical_pattern_radial_ibp {n : ℕ}
    (μ : Measure (NormalizedSpin (n+1))) [IsProbabilityMeasure μ]
    (f : Jet3) {h : NormalizedSpin (n+1)→ℝ}
    (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hhA : ∀ x,|h x|≤A) :
    let b := gaussianField (n+1) (fun i (x : NormalizedSpin (n+1)) => x.val i)
    let H := fun g x => h x+f.f (b g x)
    (∫ g,gibbsReplicaMean μ (H g) 1 (fun x => b g (x 0)*f.d1 (b g (x 0)))
      ∂Measure.pi (fun _ => gaussianReal 0 1))=
    ∫ g,gibbsReplicaMean μ (H g) 1 (fun x => f.d2 (b g (x 0))+f.d1 (b g (x 0))^2)-
      gibbsReplicaMean μ (H g) 2 (fun x => spinOverlap (x 0) (x 1)*f.d1 (b g (x 0))*f.d1 (b g (x 1)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let v := fun i (x : NormalizedSpin (n+1)) => x.val i
  let w := fun i (x : Fin 1→NormalizedSpin (n+1)) => v i (x 0)
  have hv : ∀ i,Measurable (v i) := fun i => by dsimp [v]; fun_prop
  have hw : ∀ i,Measurable (w i) := fun i => by dsimp [w,v]; fun_prop
  have hK (x : Fin 1→NormalizedSpin (n+1)) (y : NormalizedSpin (n+1)) :
      (∑ i,w i x*v i y)=spinOverlap (x 0) y := by simp only [w,v,spinOverlap_sum]
  have hb (g : Fin (n+1)→ℝ) (x : Fin 1→NormalizedSpin (n+1)) :
      (∑ i,g i*w i x)=gaussianField (n+1) v g (x 0) := rfl
  have he := nonlinear_pattern_direction_ibp μ (0:Fin 1) f hv hh hw hA
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) hhA
    (fun i x => normalizedSpin_coord_bound x i) (fun i x => normalizedSpin_coord_bound (x 0) i)
  dsimp only at he
  simp_rw [hK,hb] at he
  convert he using 1
  · congr 1; funext g; congr 1; funext x; ring
  · congr 1; funext g
    simp only [Nat.cast_one,one_mul,Fin.sum_univ_one,spinOverlap_self,Fin.succ_zero_eq_one,mul_one]
    congr 1
    · congr 1; funext x; ring
    · congr 1; funext x
      rw [show spinOverlap (x 1) (x 0)=spinOverlap (x 0) (x 1) from real_inner_comm _ _]
      ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma freshRadial_measurable (N : ℕ) (f : Jet3) : Measurable (Function.uncurry (freshRadial N f)) := by
  have hc : Continuous (Function.uncurry (freshRadial N f)) := by unfold freshRadial Function.uncurry; fun_prop
  exact hc.measurable
lemma freshSecond_measurable (N : ℕ) (f : Jet3) : Measurable (Function.uncurry (freshSecond N f)) := by
  have hc : Continuous (Function.uncurry (freshSecond N f)) := by unfold freshSecond Function.uncurry; fun_prop
  exact hc.measurable
lemma freshRadialPair_measurable (N : ℕ) (f : Jet3) : Measurable (Function.uncurry (freshRadialPair N f)) := by
  have hc : Continuous (Function.uncurry (freshRadialPair N f)) := by unfold freshRadialPair spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma freshRadial_bound (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) :
    |freshRadial N f b x|≤‖f.d1‖*‖b‖ := by
  unfold freshRadial
  rw [abs_mul,mul_comm]
  exact mul_le_mul (f.d1.norm_coe_le_norm _) (normalizedSpin_inner_bound (x 0) b) (abs_nonneg _) (norm_nonneg _)
lemma freshSecond_bound (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) :
    |freshSecond N f b x|≤‖f.d2‖+‖f.d1‖^2 := by
  apply (abs_add_le _ _).trans
  apply add_le_add (f.d2.norm_coe_le_norm _)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (f.d1.norm_coe_le_norm _) 2
lemma freshRadialPair_bound (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 2→NormalizedSpin N) :
    |freshRadialPair N f b x|≤‖f.d1‖^2 := by
  unfold freshRadialPair
  rw [abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (spinOverlap_abs_le (x 0) (x 1))
    (f.d1.norm_coe_le_norm (inner ℝ (x 0).val b)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1))
    (f.d1.norm_coe_le_norm (inner ℝ (x 1).val b)) (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma fresh_radial_ibp (n : ℕ) (f : Jet3)
    {h : NormalizedSpin (n+1)→ℝ} (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hb : ∀ x,|h x|≤A) :
    (∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 1 (freshRadial (n+1) f b) ∂stdGaussian (Spin (n+1))) =
    ∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 1 (freshSecond (n+1) f b)-
      gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshRadialPair (n+1) f b) ∂stdGaussian (Spin (n+1)) := by
  have hH : Measurable (Function.uncurry (fun b : Spin (n+1) => fun x : NormalizedSpin (n+1) => h x+f.f (inner ℝ x.val b))) :=
    (hh.comp measurable_snd).add (f.f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst))
  have h1 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshRadial_measurable (n+1) f)
  have h2 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshSecond_measurable (n+1) f)
  have h3 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshRadialPair_measurable (n+1) f)
  have h23 : AEStronglyMeasurable (fun b : Spin (n+1) =>
      gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 1 (freshSecond (n+1) f b)-
      gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshRadialPair (n+1) f b))
      (Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)) :=
    (h2.sub h3).aestronglyMeasurable
  rw [←map_pi_eq_stdGaussian,integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h1.aestronglyMeasurable,
    integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h23]
  have he := spherical_pattern_radial_ibp (unitSphereLaw (n+1)) f hh hA hb
  unfold freshRadial freshSecond freshRadialPair
  convert he using 1 <;>
    simp only [gaussianField,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]

lemma bulk_radial_last_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+1) f.f v 1 (fun a => freshRadial (n+1) f (bulkSeparateLast (n+1) M a).2) =
      bulkReplicaMean n (M+1) f.f v 1 (fun a => freshSecond (n+1) f (bulkSeparateLast (n+1) M a).2)-
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshRadialPair (n+1) f (bulkSeparateLast (n+1) M a).2) := by
  have hD : Integrable (fun b : Spin (n+1) => ‖f.d1‖*‖b‖) (stdGaussian (Spin (n+1))) :=
    ((((IsGaussian.memLp_id (stdGaussian (Spin (n+1))) 2 (by simp)).norm).integrable (by norm_num))).const_mul _
  rw [bulkReplicaMean_last_integral n M 1 f.f v _ (freshRadial_measurable _ _) hD (fun _ => by positivity) (freshRadial_bound _ _),
    bulkReplicaMean_last_integral n M 1 f.f v _ (freshSecond_measurable _ _) (integrable_const _) (fun _ => by positivity) (freshSecond_bound _ _),
    bulkReplicaMean_last_integral n M 2 f.f v _ (freshRadialPair_measurable _ _) (integrable_const _) (fun _ => by positivity) (freshRadialPair_bound _ _)]
  let P := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 1 (freshSecond (n+1) f p.2)
  let T := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 2 (freshRadialPair (n+1) f p.2)
  have hiP : Integrable P ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 1 f.f v _ (freshSecond_measurable _ _)
      (integrable_const _) (fun _ => by positivity) (freshSecond_bound _ _)
  have hiT : Integrable T ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 2 f.f v _ (freshRadialPair_measurable _ _)
      (integrable_const _) (fun _ => by positivity) (freshRadialPair_bound _ _)
  calc
    _ = ∫ a : BulkDisorder (n+1) M, ∫ b : Spin (n+1), P (a,b)-T (a,b)
        ∂stdGaussian (Spin (n+1)) ∂bulkDisorderLaw (n+1) M := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => fresh_radial_ibp n f
        (bulkHamiltonian_section_measurable _ _ _ _ a)
        (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖ by unfold bulkFeatureBound; positivity)
        (bulkHamiltonian_bound (n+1) M f.f v a)
    _ = _ := by
      have hiPT : Integrable (fun p => P p-T p) ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) := hiP.sub hiT
      rw [←integral_prod _ hiPT,integral_sub hiP hiT,integral_prod _ hiP,integral_prod _ hiT]

lemma bulk_radial_row_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (j : Fin (M+1)) :
    bulkReplicaMean n (M+1) f.f v 1 (fun a => freshRadial (n+1) f (WithLp.toLp 2 (a.1 j))) =
      bulkReplicaMean n (M+1) f.f v 1 (fun a => freshSecond (n+1) f (WithLp.toLp 2 (a.1 j)))-
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshRadialPair (n+1) f (WithLp.toLp 2 (a.1 j))) := by
  rw [bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshRadial_measurable _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshSecond_measurable _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshRadialPair_measurable _ _)]
  exact bulk_radial_last_ibp n M f v

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialIdentity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators BoundedContinuousFunction Topology

lemma bulkReplicaMean_sub_bounded (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (A B : ℝ) (hA : ∀ a x,|F a x|≤A) (hB : ∀ a x,|G a x|≤B) :
    bulkReplicaMean n M f v r (fun a x => F a x-G a x)=
      bulkReplicaMean n M f v r F-bulkReplicaMean n M f v r G := by
  rw [bulkReplicaMean_annealed _ _ _ _ _ _ (hF.sub hG) (A+B)
    (fun a x => (abs_sub _ _).trans (add_le_add (hA a x) (hB a x))),
    bulkReplicaMean_annealed _ _ _ _ _ _ hF A hA,
    bulkReplicaMean_annealed _ _ _ _ _ _ hG B hB]
  exact integral_sub (bulkReplicaPrefix_integrable _ _ _ _ _ F hF A hA)
    (bulkReplicaPrefix_integrable _ _ _ _ _ G hG B hB)

lemma bulkFreshRow_measurable (n M r : ℕ) (j : Fin M) :
    Measurable (fun p : BulkDisorder (n+1) M×(Fin r→NormalizedSpin (n+1)) => (WithLp.toLp 2 (p.1.1 j),p.2)) :=
  (((PiLp.continuous_toLp 2 _).measurable.comp ((measurable_pi_apply j).comp
    (measurable_fst.comp measurable_fst))).prodMk measurable_snd)

lemma bulkRadialRow_measurable (n M : ℕ) (f : Jet3) (j : Fin M) :
    Measurable (Function.uncurry (bulkRadialRow n M f j)) :=
  (freshRadial_measurable (n+1) f).comp (bulkFreshRow_measurable n M 1 j)
lemma bulkSecondRow_measurable (n M : ℕ) (f : Jet3) (j : Fin M) :
    Measurable (Function.uncurry (bulkSecondRow n M f j)) :=
  by unfold bulkSecondRow freshSecond Function.uncurry; fun_prop
lemma bulkRadialPairRow_measurable (n M : ℕ) (f : Jet3) (j : Fin M) :
    Measurable (Function.uncurry (bulkRadialPairRow n M f j)) :=
  by unfold bulkRadialPairRow freshRadialPair spinOverlap Function.uncurry; fun_prop

lemma bulkRadialRow_bound (n M : ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ))
    (j : Fin M) (a : BulkDisorder (n+1) M) (x : Fin 1→NormalizedSpin (n+1)) :
    |bulkRadialRow n M f j a x|≤‖f.radialMark hf‖ := (f.radialMark hf).norm_coe_le_norm _

lemma bulk_radial_difference (n M : ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) (j : Fin M) :
    bulkReplicaMean n M f.f v 1 (fun a x => bulkSecondRow n M f j a x-bulkRadialRow n M f j a x)=
      bulkReplicaMean n M f.f v 2 (bulkRadialPairRow n M f j) := by
  rw [bulkReplicaMean_sub_bounded n M 1 f.f v _ _ (bulkSecondRow_measurable n M f j)
    (bulkRadialRow_measurable n M f j) (‖f.d2‖+‖f.d1‖^2) ‖f.radialMark hf‖
    (fun a x => freshSecond_bound _ _ _ _) (bulkRadialRow_bound n M f hf j)]
  have hi : bulkReplicaMean n M f.f v 1 (bulkRadialRow n M f j)=
    bulkReplicaMean n M f.f v 1 (bulkSecondRow n M f j)-bulkReplicaMean n M f.f v 2 (bulkRadialPairRow n M f j) := by
    cases M with
    | zero => exact Fin.elim0 j
    | succ M => exact bulk_radial_row_ibp n M f v j
  linarith

lemma bulk_radial_sum_eq (n M : ℕ) (f : Jet3) (a : BulkDisorder (n+1) M) (x : Fin 1→NormalizedSpin (n+1)) :
    bulkC (n+1) M f a.1 (x 0)+bulkB (n+1) M f a.1 (x 0) (x 0)=
      ((n+1:ℕ):ℝ)⁻¹*∑ j : Fin M,(bulkSecondRow n M f j a x-bulkRadialRow n M f j a x) := by
  simp only [bulkC,bulkB,bulkSecondRow,bulkRadialRow,freshSecond,freshRadial,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bulk_radial_pair_sum_eq (n M : ℕ) (f : Jet3) (a : BulkDisorder (n+1) M) (x : Fin 2→NormalizedSpin (n+1)) :
    spinOverlap (x 0) (x 1)*bulkB (n+1) M f a.1 (x 0) (x 1)=
      ((n+1:ℕ):ℝ)⁻¹*∑ j : Fin M,bulkRadialPairRow n M f j a x := by
  simp only [bulkB,bulkRadialPairRow,freshRadialPair,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,star_trivial]
  rw [mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bulk_radial_sum_identity (n M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    bulkReplicaMean n M f.f v 1 (fun a x => bulkC (n+1) M f a.1 (x 0)+
      bulkB (n+1) M f a.1 (x 0) (x 0))=
    bulkReplicaMean n M f.f v 2 (fun a x => spinOverlap (x 0) (x 1)*
      bulkB (n+1) M f a.1 (x 0) (x 1)) := by
  simp_rw [bulk_radial_sum_eq,bulk_radial_pair_sum_eq]
  rw [bulkReplicaMean_const_mul,bulkReplicaMean_const_mul]
  congr 1
  rw [bulkReplicaMean_sum n M 1 f.f v Finset.univ (fun j a x => bulkSecondRow n M f j a x-bulkRadialRow n M f j a x)
      (fun j _ => (bulkSecondRow_measurable n M f j).sub (bulkRadialRow_measurable n M f j))
      (fun _ => ‖f.d2‖+‖f.d1‖^2+‖f.radialMark hf‖)
      (fun _ _ => by positivity) (fun j _ a x => (abs_sub _ _).trans
        (add_le_add (freshSecond_bound _ _ _ _) (bulkRadialRow_bound n M f hf j a x))),
    bulkReplicaMean_sum n M 2 f.f v Finset.univ (bulkRadialPairRow n M f)
      (fun j _ => bulkRadialPairRow_measurable n M f j) (fun _ => ‖f.d1‖^2)
      (fun _ _ => by positivity) (fun j _ a x => freshRadialPair_bound _ _ _ _)]
  exact Finset.sum_congr rfl fun j _ => bulk_radial_difference n M f hf v j

lemma bulkReplicaMean_add_bounded (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (A B : ℝ) (hA : ∀ a x,|F a x|≤A) (hB : ∀ a x,|G a x|≤B) :
    bulkReplicaMean n M f v r (fun a x => F a x+G a x)=
      bulkReplicaMean n M f v r F+bulkReplicaMean n M f v r G := by
  rw [bulkReplicaMean_annealed _ _ _ _ _ _ (hF.add hG) (A+B)
    (fun a x => (abs_add_le _ _).trans (add_le_add (hA a x) (hB a x))),
    bulkReplicaMean_annealed _ _ _ _ _ _ hF A hA,
    bulkReplicaMean_annealed _ _ _ _ _ _ hG B hB]
  exact integral_add (bulkReplicaPrefix_integrable _ _ _ _ _ F hF A hA)
    (bulkReplicaPrefix_integrable _ _ _ _ _ G hG B hB)

lemma bulkReplicaMean_mean_square_le (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) (A : ℝ) (hA : 0≤A) (hb : ∀ a x,|F a x|≤A) (c : ℝ) :
    (bulkReplicaMean n M f v r F-c)^2≤
      bulkReplicaMean n M f v r (fun a x => (F a x-c)^2) := by
  rw [bulkReplicaMean_centered_square n M f v r F hF A hA hb c]
  have hme : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => F p.1 (fun i : Fin r=>p.2 i.val)) :=
    hF.comp (measurable_fst.prodMk (Measurable.of_eval fun coordinate =>
      (measurable_pi_apply coordinate.val).comp measurable_snd))
  have hp : MemLp (fun p => F p.1 (fun i : Fin r=>p.2 i.val)) 2 (bulkAnnealedReplicaLaw n M f v) :=
    MemLp.of_bound hme.aestronglyMeasurable A (ae_of_all _ fun p=>by simpa only [Real.norm_eq_abs] using hb p.1 (fun i=>p.2 i.val))
  have hvv := variance_nonneg (fun p => F p.1 (fun i : Fin r=>p.2 i.val)) (bulkAnnealedReplicaLaw n M f v)
  rw [variance_eq_sub hp] at hvv
  rw [bulkReplicaMean_annealed n M f v r F hF A hb,
    bulkReplicaMean_annealed n M f v r (fun a x => (F a x)^2) (hF.pow_const 2) (A^2)
      (fun a x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb a x) 2)]
  simp only [Pi.pow_apply] at hvv
  nlinarith

lemma bulkReplicaMean_L2_tendsto (N M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ) (r : ℕ)
    (F : (n : ℕ)→BulkDisorder (N n+1) (M n)→(Fin r→NormalizedSpin (N n+1))→ℝ)
    (hF : ∀ n,Measurable (Function.uncurry (F n))) (A : ℕ→ℝ) (hA : ∀ n,0≤A n)
    (hb : ∀ n a x,|F n a x|≤A n) (c : ℝ)
    (hl : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) r (fun a x => (F n a x-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) r (F n)) atTop (𝓝 c) := by
  have hb' n : |bulkReplicaMean (N n) (M n) f (v n) r (F n)-c|≤
      Real.sqrt (bulkReplicaMean (N n) (M n) f (v n) r (fun a x => (F n a x-c)^2)) := by
    have he := bulkReplicaMean_mean_square_le (N n) (M n) r f (v n) (F n) (hF n) (A n) (hA n) (hb n) c
    exact Real.abs_le_sqrt he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun n=>abs_nonneg _) hb' (by simpa only [Real.sqrt_zero] using hl.sqrt)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction BigOperators Matrix

lemma bulk_single_mean_of_L2 (N M : ℕ→ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ) (c : ℝ)
    (hl : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) 1
      (fun a x=>(bulkSingleAverage (N n) (M n) w a x-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun n=>bulkReplicaMean (N n) (M n) f (v n) 1
      (bulkSingleAverage (N n) (M n) w)) atTop (𝓝 c) :=
  bulkReplicaMean_L2_tendsto N M f v 1 (fun n=>bulkSingleAverage (N n) (M n) w)
    (fun n=>bulkSingleAverage_measurable _ _ _) (fun n=>(M n:ℝ)/(N n+1:ℕ)*‖w‖)
    (fun n=>by positivity) (fun n=>bulkSingleAverage_bound _ _ _) c hl

lemma bulk_diagonal_mean_add (n M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    bulkReplicaMean n M f.f v 1 (fun a x=>bulkC (n+1) M f a.1 (x 0)+
      bulkB (n+1) M f a.1 (x 0) (x 0))=
    bulkReplicaMean n M f.f v 1 (bulkSingleAverage n M (f.dilationMark hf))+
      bulkReplicaMean n M f.f v 1 (bulkSingleAverage n M (f.d1*f.d1)) := by
  change bulkReplicaMean n M f.f v 1 (fun a x=>bulkSingleAverage n M (f.dilationMark hf) a x+
      bulkSingleAverage n M (f.d1*f.d1) a x)=_
  exact bulkReplicaMean_add_bounded n M 1 f.f v _ _
    (bulkSingleAverage_measurable _ _ _) (bulkSingleAverage_measurable _ _ _) _ _
    (bulkSingleAverage_bound _ _ _) (bulkSingleAverage_bound _ _ _)

lemma bulk_radial_limit_relation (N M : ℕ→ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ) (c d : ℝ)
    (hc : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f.f (v n) 1
      (fun a x=>(bulkC (N n+1) (M n) f a.1 (x 0)-c)^2)) atTop (𝓝 0))
    (hd : Tendsto (fun n=>bulkReplicaMean (N n) (M n) f.f (v n) 1
      (fun a x=>(bulkB (N n+1) (M n) f a.1 (x 0) (x 0)-d)^2)) atTop (𝓝 0))
    (K : ℝ) (hK : ∀ n,(M n:ℝ)/(N n+1:ℕ)*‖f.d1‖^2≤K)
    (μ : ProbabilityMeasure (BulkPairRange K))
    (hl : Tendsto (fun n=>bulkPairLaw (N n) (M n) f.f f.d1 (v n) K (hK n)) atTop (𝓝 μ)) :
    c+d=∫ p,p.1.val*p.2.val ∂(μ : Measure (BulkPairRange K)) := by
  have hcm := bulk_single_mean_of_L2 N M f.f (f.dilationMark hf) v c hc
  have hdm := bulk_single_mean_of_L2 N M f.f (f.d1*f.d1) v d hd
  have hs := hcm.add hdm
  have he n := bulk_diagonal_mean_add (N n) (M n) f hf (v n)
  simp_rw [←he,bulk_radial_sum_identity _ _ f hf] at hs
  let F : BulkPairRange K→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun p=>p.1.val*p.2.val,by fun_prop⟩
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hl
  have htest n : (∫ p,F p ∂(bulkPairLaw (N n) (M n) f.f f.d1 (v n) K (hK n) : Measure _))=
      bulkReplicaMean (N n) (M n) f.f (v n) 2
        (fun a x=>spinOverlap (x 0) (x 1)*bulkB (N n+1) (M n) f a.1 (x 0) (x 1)) := by
    rw [bulkPairLaw_integral]
    congr 1
    funext a x
    change spinOverlap (x 1) (x 0)*bulkPairAverage (N n) (M n) f.d1 a x=_
    rw [←bulkB_pairAverage]
    congr 1
    exact real_inner_comm _ _
  change Tendsto (fun n=>∫ p,F p ∂(bulkPairLaw (N n) (M n) f.f f.d1 (v n) K (hK n) : Measure _)) atTop _ at ht
  simp_rw [htest] at ht
  exact tendsto_nhds_unique hs ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayLawExt
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

lemma array_law_eq_of_blocks {K : Type*} [MeasurableSpace K]
    (μ ν : Measure (CompactArray K)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (compactBlock (n+1)) = ν.map (compactBlock (n+1))) : μ = ν := by
  let e : CompactArray K ≃ᵐ (ℕ × ℕ → K) := (MeasurableEquiv.curry ℕ ℕ K).symm
  apply e.map_measurableEquiv_injective
  let P (I : Finset (ℕ × ℕ)) := (ν.map e).map I.restrict
  have hp : IsProjectiveLimit (ν.map e) P := fun _ => rfl
  apply IsProjectiveLimit.unique (P := P) ?_ hp
  intro I
  let n := I.sup (fun a => max a.1 a.2)
  have hb (a : I) : a.val.1 < n+1 ∧ a.val.2 < n+1 := by
    have he : max a.val.1 a.val.2 ≤ n := Finset.le_sup (f := fun a : ℕ × ℕ => max a.1 a.2) a.property
    exact ⟨by omega,by omega⟩
  let G : CompactBlock K (n+1) → (I → K) :=
    fun B a => B ⟨a.val.1,(hb a).1⟩ ⟨a.val.2,(hb a).2⟩
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro a
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hm : Measurable (compactBlock (K:=K) (n+1)) := by
    unfold compactBlock
    exact Measurable.of_eval fun _ => Measurable.of_eval fun _ => by fun_prop
  change (μ.map e).map I.restrict = (ν.map e).map I.restrict
  have he : I.restrict ∘ e = G ∘ compactBlock (n+1) := by
    funext Q a
    rfl
  rw [Measure.map_map I.measurable_restrict e.measurable,
    Measure.map_map I.measurable_restrict e.measurable,he,
    ← Measure.map_map hG hm,← Measure.map_map hG hm,h n]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_OrderedCode
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

lemma orderedLevelCode_mono {k : ℕ} (v : Fin (k+1) → ℝ) :
    Monotone (orderedLevelCode v) := by
  intro x y hxy
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact hi.trans hxy

lemma orderedLevelCode_value {k : ℕ} (v : Fin (k+1) → ℝ) (hv : StrictMono v)
    (j : Fin (k+1)) : orderedLevelCode v (v j) = j := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
    exact hv.le_iff_le.mp hi
  · exact Finset.le_sup (f := id) (by simp)

lemma orderedLevelCode_top {k : ℕ} (v : Fin (k+1) → ℝ) (x : ℝ)
    (hv : v (Fin.last k) ≤ x) : orderedLevelCode v x = Fin.last k := by
  apply le_antisymm (Fin.le_last _)
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)

lemma orderedLevelCode_measurable {k : ℕ} (v : Fin (k+1) → ℝ) :
    Measurable (orderedLevelCode v) := (orderedLevelCode_mono v).measurable

lemma roundLower_one (n : ℕ) : roundLower n 1 = 1 := by
  unfold roundLower
  simp only [mul_one,Nat.floor_natCast]
  exact div_self (by positivity)

lemma orderedRoundCode_label (q : BoundedField 1) (n : ℕ) :
    (fun u => orderedLevelCode (strictRoundModel q n).value (roundLower n (q u)))
      =ᵐ[timeLaw] (strictRoundModel q n).label := by
  filter_upwards [(strictRoundModel q n).agrees] with u hu
  change (strictRoundModel q n).value ((strictRoundModel q n).label u) =
    roundLower n (q u) at hu
  rw [←hu,orderedLevelCode_value _ (strictRoundModel_strict q n)]

lemma orderedRoundCode_one (q : BoundedField 1) (n : ℕ) :
    orderedLevelCode (strictRoundModel q n).value (roundLower n 1) =
      Fin.last (strictRoundModel q n).depth := by
  rw [roundLower_one]
  apply orderedLevelCode_top
  exact (roundTimeValue q n _).property.2

lemma compactGG_events_general {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (n : ℕ) (hn : 0<n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ),
      compactGGDefect μ n i f g=0)
    (s : Set (CompactBlock K n)) (hs : MeasurableSet s)
    (t : Set K) (ht : MeasurableSet t) :
    (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray K | Q 0 1∈t}/n+
      (∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}))/n := by
  classical
  have he := congrArg (fun ρ : Measure (CompactBlock K n × K) =>
    ρ.real (s×ˢt)) (compactGG_joint_law μ hn i hGG)
  have hb := (compactBlock_continuous (K:=K) n).measurable
  have hm (i j : ℕ) : Measurable (fun Q : CompactArray K => Q i j) := by fun_prop
  rw [map_measureReal_apply (hb.prodMk (hm _ _)) (hs.prod ht),
    measureReal_nnreal_smul_apply,measureReal_add_apply] at he
  have hsum : (∑ j ∈ Finset.univ.erase i,
      (μ : Measure _).map (fun Q => (compactBlock n Q,Q i j))).real (s×ˢt) =
      ∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}) := by
    simp only [measureReal_def,Measure.finsetSum_apply]
    rw [ENNReal.toReal_sum (by intro _ _; finiteness)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Measure.map_apply (hb.prodMk (hm _ _)) (hs.prod ht)]
    rfl
  rw [hsum] at he
  have hprod : (((μ : Measure _).map (compactBlock n)).prod
      ((μ : Measure _).map (fun Q : CompactArray K => Q 0 1))).real (s×ˢt) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray K | Q 0 1∈t} := by
    simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      Measure.map_apply hb hs,Measure.map_apply (hm 0 1) ht]
    rfl
  rw [hprod] at he
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at he
  change (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) = (n:ℝ)⁻¹*(_+_) at he
  rw [he]
  ring

variable {K L : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

omit [TopologicalSpace K] [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
  [Fintype L] [MeasurableSingletonClass L] in
lemma finiteCodeArray_measurable {χ : K → L} (hχ : Measurable χ) :
    Measurable (finiteCodeArray χ) := by
  unfold finiteCodeArray
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

omit [TopologicalSpace K] [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
  [Fintype L] [MeasurableSingletonClass L] in
lemma finiteCodeBlock_measurable {χ : K → L} (hχ : Measurable χ) (n : ℕ) :
    Measurable (finiteCodeBlock (n:=n) χ) := by
  unfold finiteCodeBlock
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma compactGG_finite_pushforward_general (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ)
      (g : K →ᵇ ℝ), compactGGDefect μ n i f g=0)
    {χ : K → L} (hχ : Measurable χ) :
    FiniteGG ((μ : Measure (CompactArray K)).map (finiteCodeArray χ)) := by
  classical
  intro n hn i A c
  have hm := finiteCodeArray_measurable hχ
  have hb := finiteBlock_measurable (L:=L) n
  have he (a b : ℕ) : Measurable (fun R : FiniteOverlap L => R a b) := by fun_prop
  have hs : MeasurableSet {R : FiniteOverlap L | finiteBlock n R=A} :=
    measurableSet_eq_fun hb measurable_const
  have hv (a b : ℕ) : MeasurableSet {R : FiniteOverlap L | R a b=c} :=
    measurableSet_eq_fun (he a b) measurable_const
  have hvv (a b : ℕ) : MeasurableSet {R : FiniteOverlap L | finiteBlock n R=A ∧ R a b=c} := hs.inter (hv a b)
  rw [map_measureReal_apply hm (hvv _ _),map_measureReal_apply hm hs,
    map_measureReal_apply hm (hv 0 1)]
  simp_rw [map_measureReal_apply hm (hvv _ _)]
  exact compactGG_events_general μ n (by omega) i (hGG n i)
    ((finiteCodeBlock χ) ⁻¹' {A}) ((measurableSet_singleton A).preimage (finiteCodeBlock_measurable hχ n))
    (χ ⁻¹' {c}) ((measurableSet_singleton c).preimage hχ)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

lemma roundedLevelCode_measurable (q : BoundedField 1) (n : ℕ) :
    Measurable (roundedLevelCode q n) :=
  (orderedLevelCode_measurable _).comp ((roundLower_measurable n).comp measurable_subtype_coe)

lemma roundedLevelCode_mono (q : BoundedField 1) (n : ℕ) : Monotone (roundedLevelCode q n) :=
  (orderedLevelCode_mono _).comp ((roundLower_monotone n).comp (Subtype.mono_coe _))

theorem indexedDepthLaw_eq_rounded_bulk
    (μ : ProbabilityMeasure (CompactArray Time)) (q : Time → Time) (hq : Monotone q)
    (hpair : (μ : Measure (CompactArray Time)).map (fun Q => Q 0 1) = timeLaw.map q)
    (hGG : ∀ n (i : Fin n) (F : CompactBlock Time n →ᵇ ℝ) (g : Time →ᵇ ℝ),
      compactGGDefect μ n i F g = 0)
    (hgeo : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l) (n : ℕ) :
    (indexedDepthLaw (strictRoundModel (unitQuantileField q hq) n).depth
      (stepCumulative (strictRoundModel (unitQuantileField q hq) n).weight) :
        Measure (FiniteOverlap (Fin ((strictRoundModel (unitQuantileField q hq) n).depth+1)))) =
      (μ : Measure (CompactArray Time)).map (finiteCodeArray (roundedLevelCode (unitQuantileField q hq) n)) := by
  let f := unitQuantileField q hq
  let M := strictRoundModel f n
  let χ := roundedLevelCode f n
  let ν := (μ : Measure (CompactArray Time)).map (finiteCodeArray χ)
  let ρ := (indexedDepthLaw M.depth (stepCumulative M.weight) :
    Measure (FiniteOverlap (Fin (M.depth+1))))
  have hm := finiteCodeArray_measurable (roundedLevelCode_measurable f n)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = Fin.last M.depth) ∧
      ∀ i j l, min (R i j) (R i l) ≤ R j l := by
    apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    filter_upwards [hgeo] with Q hQ
    refine ⟨fun i j => congrArg χ (hQ.1 i j),?_,?_⟩
    · intro i
      change χ (Q i i) = _
      rw [hQ.2.1 i]
      exact orderedRoundCode_one f n
    · intro i j l
      have hχ : Monotone χ := roundedLevelCode_mono f n
      have hx := hχ (hQ.2.2 i j l)
      change min (χ (Q i j)) (χ (Q i l)) ≤ χ (Q j l)
      by_cases hab : Q i j ≤ Q i l
      · simpa only [min_eq_left hab,min_eq_left (hχ hab)] using hx
      · have hba := le_of_not_ge hab
        simpa only [min_eq_right hba,min_eq_right (hχ hba)] using hx
  have hp : ν.map (fun R => R 0 1) = timeLaw.map M.label := by
    change ((μ : Measure (CompactArray Time)).map (finiteCodeArray χ)).map _ = _
    rw [Measure.map_map (by fun_prop) hm]
    have he : (fun R : FiniteOverlap (Fin (M.depth+1)) => R 0 1) ∘ finiteCodeArray χ =
        χ ∘ (fun Q : CompactArray Time => Q 0 1) := rfl
    rw [he,← Measure.map_map (roundedLevelCode_measurable f n) (by fun_prop),hpair,
      Measure.map_map (roundedLevelCode_measurable f n) hq.measurable]
    apply Measure.map_congr
    exact orderedRoundCode_label f n
  have hpa (c : Fin (M.depth+1)) : ρ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c} := by
    have hh := congrArg (fun η : Measure (Fin (M.depth+1)) => η.real {c}) hp
    rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton c),
      map_measureReal_apply M.measurable_label (measurableSet_singleton c)] at hh
    rw [indexedDepthLaw_pair_weights M.depth M.weight M.weight_pos M.weight_sum]
    exact hh.symm
  apply array_law_eq_of_blocks ρ ν
  exact finiteGG_block_law_unique ρ ν (Fin.last M.depth)
    (indexedDepthLaw_geometry M.depth _) hν
    (indexedDepthLaw_finiteGG M.depth _ (stepCumulative_strictMono M.weight M.weight_pos)
      (stepCumulative_pos M.weight M.weight_pos) (stepCumulative_lt_one M.weight M.weight_pos M.weight_sum))
    (compactGG_finite_pushforward_general μ hGG (roundedLevelCode_measurable f n)) hpa

lemma depthMarkedDecode_measurable {K : Type*} [MeasurableSpace K] {k : ℕ}
    (p : Fin (k+1) → K) (D : K) : Measurable (depthMarkedDecode p D) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold depthMarkedDecode
  split_ifs
  · exact measurable_const
  · exact (measurable_of_countable p).comp ((measurable_pi_apply j).comp (measurable_pi_apply i))

lemma gibbsProbabilityKernel_zero {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] :
    gibbsProbabilityKernel κ (fun _ _ => 0) = κ := by
  ext a : 1
  rw [gibbsProbabilityKernel_of_integrable κ (fun _ _ => 0) measurable_const a (integrable_const _)]
  simp only [tiltLaw,tiltPartition,mul_zero,Real.exp_zero,integral_const,probReal_univ,one_smul,
    ENNReal.ofReal_one,inv_one]
  exact withDensity_one

lemma annealedInfiniteReplicaMeasure_zero {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P] :
    annealedInfiniteReplicaMeasure κ P (fun _ _ => 0) measurable_const =
      P ⊗ₘ kernelInfiniteReplica κ ℕ := by
  simp only [annealedInfiniteReplicaMeasure,gibbsProbabilityKernel_zero]

theorem cavityLabelMarkedLaw_eq_depth {K : ℝ} {k : ℕ}
    (p : Fin (k+1) → BulkPairRange K) (D : BulkPairRange K) (z : Fin k → ℝ) :
    (cavityLabelMarkedLaw p D z : Measure (CompactArray (BulkPairRange K))) =
      (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))).map (depthMarkedDecode p D) := by
  change Measure.map (fun a : IndexedCascadeBase k × (ℕ → IndexedLeaf k) =>
      cavityLabelMarkedArray p D a.2)
    (annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _ => 0) _) = _
  rw [annealedInfiniteReplicaMeasure_zero]
  change _ = ((indexedInfiniteLeafMeasure k z).map (fun a => indexedDepthArray k a.2)).map _
  have hm : Measurable (fun a : IndexedCascadeBase k × (ℕ → IndexedLeaf k) =>
    indexedDepthArray k a.2) := (indexedDepthArray_measurable k).comp measurable_snd
  rw [Measure.map_map (depthMarkedDecode_measurable p D) hm]
  apply congrArg (fun F => (indexedInfiniteLeafMeasure k z).map F)
  funext a i j
  simp only [Function.comp_def,cavityLabelMarkedArray,depthMarkedDecode,indexedDepthArray,
    indexedCommonDepth_comm k (a.2 i) (a.2 j)]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedCoupling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma timeGridRound_tendsto (r : Time) :
    Tendsto (fun n => timeGridRound n r) atTop (𝓝 r) :=
  roundTime_tendsto id monotone_id r

lemma roundedTimeValue_code_ae (q : Time → Time) (hq : Monotone q) (n : ℕ) :
    ∀ᵐ r ∂timeLaw.map q,
      roundTimeValue (unitQuantileField q hq) n (roundedLevelCode (unitQuantileField q hq) n r) =
        timeGridRound n r := by
  apply (ae_map_iff hq.measurable.aemeasurable (by
    apply measurableSet_eq_fun
    · exact (measurable_of_countable (roundTimeValue (unitQuantileField q hq) n)).comp
        (roundedLevelCode_measurable (unitQuantileField q hq) n)
    · exact (show Measurable (fun r : Time => roundLower n (r : ℝ)) from
        (roundLower_measurable n).comp measurable_subtype_coe).subtype_mk)).mpr
  filter_upwards [orderedRoundCode_label (unitQuantileField q hq) n,
    (strictRoundModel (unitQuantileField q hq) n).agrees] with u hu hv
  apply Subtype.ext
  change (strictRoundModel (unitQuantileField q hq) n).value
    (orderedLevelCode (strictRoundModel (unitQuantileField q hq) n).value (roundLower n (q u))) = _
  change orderedLevelCode _ (roundLower n (q u : ℝ)) = _ at hu
  rw [hu]
  exact hv

lemma roundedTimeValue_code_array_ae
    (μ : ProbabilityMeasure (CompactArray Time)) (q : Time → Time) (hq : Monotone q)
    (hpair : (μ : Measure (CompactArray Time)).map (fun Q => Q 0 1) = timeLaw.map q)
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)), ∀ i j, Q i j = Q j i)
    (he : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=Time) e)
      (μ : Measure _) (μ : Measure _)) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray Time)), ∀ n i j, i ≠ j →
      roundTimeValue (unitQuantileField q hq) n (roundedLevelCode (unitQuantileField q hq) n (Q i j)) =
        timeGridRound n (Q i j) := by
  apply ae_all_iff.mpr
  intro n
  have hp := roundedTimeValue_code_ae q hq n
  rw [←hpair] at hp
  have hp' := ae_of_ae_map (show Measurable (fun Q : CompactArray Time => Q 0 1) from by fun_prop).aemeasurable hp
  apply compact_exchangeable_offdiag_ae μ he (fun r =>
    roundTimeValue (unitQuantileField q hq) n (roundedLevelCode (unitQuantileField q hq) n r) =
      timeGridRound n r)
  filter_upwards [hp',hsy] with Q hQ hs
  simpa only [hs 1 0] using hQ

theorem cavityLabelMarkedLaw_tendsto_graph
    (μ : ProbabilityMeasure (CompactArray Time)) (q : Time → Time) (hq : Monotone q)
    (hpair : (μ : Measure (CompactArray Time)).map (fun Q => Q 0 1) = timeLaw.map q)
    (hGG : ∀ n (i : Fin n) (F : CompactBlock Time n →ᵇ ℝ) (g : Time →ᵇ ℝ),
      compactGGDefect μ n i F g = 0)
    (hgeo : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l)
    (he : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=Time) e)
      (μ : Measure _) (μ : Measure _))
    {K : ℝ} (P : Time → BulkPairRange K) (hP : Continuous P) (D : BulkPairRange K) :
    Tendsto (fun n => cavityLabelMarkedLaw
      (fun i => P (roundTimeValue (unitQuantileField q hq) n i)) D
      (stepCumulative (strictRoundModel (unitQuantileField q hq) n).weight)) atTop
      (𝓝 (μ.map (timeMarkedDecode_measurable hP.measurable D).aemeasurable)) := by
  let f := unitQuantileField q hq
  let F n := depthMarkedDecode (fun i => P (roundTimeValue f n i)) D ∘ finiteCodeArray (roundedLevelCode f n)
  let G := timeMarkedDecode P D
  have hF n : Measurable (F n) :=
    (depthMarkedDecode_measurable _ _).comp (finiteCodeArray_measurable (roundedLevelCode_measurable f n))
  have hG : Measurable G := timeMarkedDecode_measurable hP.measurable D
  have ht : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)), Tendsto (fun n => F n Q) atTop (𝓝 (G Q)) := by
    filter_upwards [roundedTimeValue_code_array_ae μ q hq hpair (hgeo.mono fun _ h => h.1) he] with Q hQ
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · simpa only [F,G,Function.comp_def,depthMarkedDecode,timeMarkedDecode,ite_eq_left hij] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => D) atTop (𝓝 D))
    · have h := hP.continuousAt.tendsto.comp (timeGridRound_tendsto (Q i j))
      convert h using 1
      · funext n
        dsimp only [F,G,Function.comp_def,depthMarkedDecode,timeMarkedDecode,finiteCodeArray]
        rw [ite_eq_right hij,hQ n i j hij]
      · simp only [G,timeMarkedDecode,ite_eq_right hij]
  have hlim := probabilityMap_tendsto_of_ae_tendsto μ F G hF hG ht
  have hl n : cavityLabelMarkedLaw (fun i => P (roundTimeValue f n i)) D
      (stepCumulative (strictRoundModel f n).weight) = μ.map (hF n).aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [cavityLabelMarkedLaw_eq_depth,indexedDepthLaw_eq_rounded_bulk μ q hq hpair hGG hgeo n,
      Measure.map_map (depthMarkedDecode_measurable _ _) (finiteCodeArray_measurable (roundedLevelCode_measurable f n))]
    rfl
  change Tendsto (fun n => cavityLabelMarkedLaw (fun i => P (roundTimeValue f n i)) D
    (stepCumulative (strictRoundModel f n).weight)) atTop (𝓝 (μ.map hG.aemeasurable))
  simpa only [hl] using hlim

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedGraphLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma markedTimePair_ae {K : ℝ} (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    {P : Time → Prop} (hP : ∀ᵐ r ∂markedTimePair K μ, P r) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), P (nonnegativeSpinTime (Q 0 1).1) := by
  have h := ae_of_ae_map (show Measurable (fun Q : CompactArray Time => Q 0 1) from by fun_prop).aemeasurable hP
  exact ae_of_ae_map (compactMapArray_continuous
    (nonnegativeSpinTime_continuous.comp (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst))).measurable.aemeasurable h

theorem marked_graph_law {K B d : ℝ} (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hB : B < 1) (hd0 : 0 ≤ d) (hdK : d ≤ K)
    (he : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=BulkPairRange K) e)
      (μ : Measure _) (μ : Measure _))
    (hn : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, 0 ≤ (Q i j).1.val)
    (hD1 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).1.val = 1)
    (hD2 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i, (Q i i).2.val = d)
    (hBd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, (Q i j).2.val ≤ d)
    (a : ℝ → ℝ) (ha0 : ∀ r, 0 ≤ a r)
    (hag : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), ∀ i j, i ≠ j → (Q i j).2.val = a (Q i j).1.val)
    (hsc : ∀ᵐ r : Time ∂markedTimePair K μ, a r.val = ∫ t in 0..r.val, (realTail (markedTimePair K μ) t)⁻¹^2)
    (hbound : ∀ᵐ r : Time ∂markedTimePair K μ, r.val ≤ B) :
    (markedTimeLaw K μ).map (timeMarkedDecode_measurable
      (continuousCavityProfile_continuous (markedTimePair K μ) hB hd0 hdK).measurable
      (cavityTrueDiagonal hd0 hdK)).aemeasurable = μ := by
  let P := continuousCavityProfile (markedTimePair K μ) B hd0 hdK
  let D := cavityTrueDiagonal hd0 hdK
  let e : BulkPairRange K → Time := fun p => nonnegativeSpinTime p.1
  have hP : Continuous P := continuousCavityProfile_continuous (markedTimePair K μ) hB hd0 hdK
  have hec : Continuous e := nonnegativeSpinTime_continuous.comp continuous_fst
  have h01 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), P (e (Q 0 1)) = Q 0 1 := by
    filter_upwards [markedTimePair_ae μ hsc,markedTimePair_ae μ hbound,hn,hBd,hag] with Q hS hBnd hN hBd hAg
    have hval : (e (Q 0 1)).val = (Q 0 1).1.val := nonnegativeSpinTime_val (hN 0 1)
    apply Prod.ext
    · exact Subtype.ext hval
    · apply Subtype.ext
      apply continuousCavityProfile_eq (markedTimePair K μ) hd0 hdK hbound hBnd
      · rw [hAg 0 1 (by omega)]; exact ha0 _
      · exact hBd 0 1
      · change a (e (Q 0 1)).val = _ at hS
        rw [hval] at hS
        rw [hAg 0 1 (by omega)]
        change a (Q 0 1).1.val = ∫ t in 0..(e (Q 0 1)).val, (realTail (markedTimePair K μ) t)⁻¹^2
        rw [hval]
        exact hS
  have h10 := (he (Equiv.swap 0 1)).quasiMeasurePreserving.ae h01
  have h10' : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))), P (e (Q 1 0)) = Q 1 0 := by
    simpa only [compactRelabel,Equiv.swap_apply_left,Equiv.swap_apply_right] using h10
  have hoff := compact_exchangeable_offdiag_ae μ he (fun p => P (e p) = p) h10'
  have hall : (timeMarkedDecode P D ∘ compactMapArray e) =ᵐ[(μ : Measure (CompactArray (BulkPairRange K)))] id := by
    filter_upwards [hoff,hD1,hD2] with Q hO hD1 hD2
    funext i j
    dsimp only [Function.comp_def,timeMarkedDecode,compactMapArray,id_eq]
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      subst j
      exact Prod.ext (Subtype.ext (hD1 i).symm) (Subtype.ext (hD2 i).symm)
    · rw [ite_eq_right hij]
      exact hO i j hij
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (timeMarkedDecode P D) (Measure.map (compactMapArray e)
    (μ : Measure (CompactArray (BulkPairRange K)))) = (μ : Measure (CompactArray (BulkPairRange K)))
  rw [Measure.map_map (timeMarkedDecode_measurable hP.measurable D)
    (compactMapArray_continuous hec).measurable,
    Measure.map_congr hall,Measure.map_id]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCavityRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma roundedCavityPair_conditions (n d : ℕ) (η : Measure Time) [IsProbabilityMeasure η]
    {B K a : ℝ} (hB : B < 1) (ha0 : 0 ≤ a) (haK : a ≤ K) (j : ℕ) :
    (∀ i, 0 ≤ cavityPairProfile n d (roundedCavityPair η B ha0 haK j) 0 i) ∧
    (∀ i, Monotone (fun l => cavityPairProfile n d (roundedCavityPair η B ha0 haK j) l i)) ∧
    (∀ i, cavityPairProfile n d (roundedCavityPair η B ha0 haK j)
      (Fin.last _) i ≤ cavityPairDiagonal n d (cavityTrueDiagonal ha0 haK) i) := by
  have h0 := fun l => continuousCavityProfile_nonneg η B ha0 haK
    (roundTimeValue (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j l)
  have hD := fun l => continuousCavityProfile_le_diagonal η B ha0 haK
    (roundTimeValue (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j l)
  refine ⟨?_,?_,?_⟩
  · intro i; cases i with
    | inl i => exact (h0 0).2
    | inr i => exact (h0 0).1
  · intro i; cases i with
    | inl i => exact (continuousCavityProfile_mono η hB ha0 haK).comp (roundTimeValue_mono _ j)
    | inr i => exact fun l m h => roundTimeValue_mono _ j h
  · intro i; cases i with
    | inl i => exact (hD (Fin.last _)).2
    | inr i => exact (hD (Fin.last _)).1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityRoundedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


lemma markedTimePair_eq_map (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    markedTimePair K μ=(μ : Measure (CompactArray (BulkPairRange K))).map
      (fun Q=>nonnegativeSpinTime (Q 0 1).1) := by
  change Measure.map (fun Q : CompactArray Time=>Q 0 1)
    (Measure.map (compactMapArray (fun p : BulkPairRange K=>nonnegativeSpinTime p.1)) (μ : Measure _))=_
  rw [Measure.map_map (by fun_prop) (by
    exact (compactMapArray_continuous (nonnegativeSpinTime_continuous.comp continuous_fst)).measurable)]
  rfl

lemma marked_cappedA_identification {K B a : ℝ}
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hB : B<1)
    (hn : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),0≤(Q 0 1).1.val)
    (hBd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),(Q 0 1).2.val≤a)
    (f : ℝ→ℝ)
    (hg : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),(Q 0 1).2.val=f (Q 0 1).1.val)
    (hsc : ∀ᵐ r : Time ∂markedTimePair K μ,f r=∫ t in 0..(r:ℝ),(realTail (markedTimePair K μ) t)⁻¹^2)
    (hbound : ∀ᵐ r : Time ∂markedTimePair K μ,(r:ℝ)≤B) :
    (∀ᵐ r : Time ∂markedTimePair K μ,cappedA (markedTimePair K μ) B r≤a) ∧
    cavityProfileMoment (markedTimePair K μ) B=
      (∫ Q,(Q 0 1).1.val*(Q 0 1).2.val ∂(μ : Measure (CompactArray (BulkPairRange K))))/2 := by
  let e:=fun Q : CompactArray (BulkPairRange K)=>nonnegativeSpinTime (Q 0 1).1
  have he : Measurable e:=(nonnegativeSpinTime_continuous.comp (by fun_prop)).measurable
  have hid : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),
      cappedA (markedTimePair K μ) B (e Q)=(Q 0 1).2.val := by
    filter_upwards [markedTimePair_ae μ hsc,markedTimePair_ae μ hbound,hn,hg] with Q hS hBd hN hG
    rw [cappedA_eq_integral (markedTimePair K μ) hbound (e Q).prop.1 hBd,←hS]
    rw [nonnegativeSpinTime_val hN]
    exact hG.symm
  have hmap : (μ : Measure (CompactArray (BulkPairRange K))).map e=markedTimePair K μ :=
    (markedTimePair_eq_map K μ).symm
  constructor
  · have hh : ∀ᵐ r : Time ∂(μ : Measure _).map e,cappedA (markedTimePair K μ) B r≤a := by
      apply (ae_map_iff he.aemeasurable (measurableSet_le
        (((cappedA_continuous (markedTimePair K μ) hB).comp continuous_subtype_val).measurable)
        measurable_const)).mpr
      filter_upwards [hid,hBd] with Q hQ hBnd
      change cappedA (markedTimePair K μ) B (e Q)≤a
      rwa [hQ]
    rwa [hmap] at hh
  · have hi:=integral_map he.aemeasurable
      (show AEStronglyMeasurable (fun r : Time=>(r:ℝ)*cappedA (markedTimePair K μ) B r/2)
        ((μ : Measure _).map e) from
        ((continuous_subtype_val.mul ((cappedA_continuous (markedTimePair K μ) hB).comp
          continuous_subtype_val)).div_const 2).measurable.aestronglyMeasurable)
    rw [hmap] at hi
    unfold cavityProfileMoment
    rw [hi,←integral_div]
    apply integral_congr_ae
    filter_upwards [hid,hn] with Q hQ hN
    rw [hQ,nonnegativeSpinTime_val hN]
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCavityData
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem bulk_cavity_data_oai (M : ℕ→ℕ) (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ))
    (v : ℕ→ℕ→ℝ) (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
    (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M n+2:ℕ):ℝ)/(n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK (s n))) atTop (𝓝 μ)) :
    Nonempty (BulkCavityData M g v s α K μ hg) := by
  have hOm:=bulk_limit_geometry M g.f v (Eventually.of_forall hv) hdO hs ho
  obtain ⟨⟨a,ha,hLa⟩,⟨c,hc,hLc⟩⟩:=bulk_diagonal_C_concentration M g hg v s hs.tendsto_atTop α hd ho
    hOm.2.2 hOm.1 hOm.2.1
  rw [abs_of_nonneg hα] at ha hc
  have hD2:=bulkMarkedArray_limit_diagonal_const (fun n=>M n+2) g v s K (fun j=>hK (s j)) μ hf a hLa
  have hmg:=bulkMarkedArray_limit_mark_geometry (fun n=>M n+2) g v s K (fun j=>hK (s j)) hf
  obtain ⟨Q,hQ,hpos⟩:=(hD2.and hmg.1).exists
  have ha0 : 0≤a:=by simpa only [hQ 0] using hpos 0
  have haK : a≤K:=by simpa only [hQ 0] using (Q 0 0).2.prop.2
  have haA : a≤α*‖g.d1‖^2:=(le_abs_self a).trans ha
  have hBd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).2.val≤a := by
    filter_upwards [hD2,hmg.2] with Q hD hG
    intro i j
    have h:=hG i j
    rw [hD i,hD j] at h
    linarith
  obtain ⟨f,_hfm,hfb,hfg,hsc,hbound⟩:=bulk_marked_self_consistency M g v hv hC hvC hdO hdF s hs α hα hd ν ho
    K hK0 (fun j=>hK (s j)) μ hf
  let η:=markedTimePair K μ
  let B:=(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  have hA0 : 0≤α*‖g.d1‖^2:=mul_nonneg hα (sq_nonneg _)
  have hB : B<1:=(div_lt_one (by linarith : 0<1+α*‖g.d1‖^2)).mpr (by linarith)
  have he e:=compact_exchangeability_limit hf e
    (fun j=>bulkMarkedArray_exchangeable (s j) (M (s j)+2) g (v (s j)) K (hK (s j)) e)
  have hp:=bulkMarkedArray_limit_overlap (fun n=>M n+2) g v s K (fun j=>hK (s j)) hf
  have hgF:=bulk_limit_geometry (fun n=>M n+2) g.f v (Eventually.of_forall hv) hdF hs hp
  have hgeom:=marked_overlap_geometry K μ he hgF.1 hgF.2.1
  have hm:=marked_cappedA_identification μ hB (hgeom.2.2.mono fun _array hQ=>hQ 0 1)
    (hBd.mono fun _array hQ=>hQ 0 1) f (hfg.mono fun _array hQ=>hQ 0 1 (by omega)) hsc hbound
  have hrad : (c+a)/2=cavityProfileMoment η B := by
    have ht:=ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hf
      (by fun_prop : Continuous (fun Q : CompactArray (BulkPairRange K)=>Q 1 0))
    simp_rw [bulkMarkedArray_pair] at ht
    have hr:=bulk_radial_limit_relation s (fun j=>M (s j)+2) g hg (fun j=>v (s j)) c a hLc hLa K
      (fun j=>hK (s j)) _ ht
    rw [ProbabilityMeasure.toMeasure_map,integral_map (by fun_prop : Measurable
      (fun Q : CompactArray (BulkPairRange K)=>Q 1 0)).aemeasurable (by fun_prop)] at hr
    have hs:=integral_map (he (Equiv.swap 0 1)).measurable.aemeasurable
      (show AEStronglyMeasurable (fun Q : CompactArray (BulkPairRange K)=>(Q 0 1).1.val*(Q 0 1).2.val)
        ((μ : Measure _).map (compactRelabel (Equiv.swap 0 1))) from by fun_prop)
    rw [(he (Equiv.swap 0 1)).map_eq] at hs
    simp only [compactRelabel,Equiv.swap_apply_left,Equiv.swap_apply_right] at hs
    rw [hm.2,hr,hs]
  have hD1:=ae_of_ae_map (compactMapArray_continuous (show Continuous
    (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable
    (bulkGibbsArray_limit_diagonal g.f (fun n=>M n+2) v s hp)
  have hgraph:=marked_graph_law μ hB ha0 haK he hgeom.2.2 hD1 hD2 hBd f
    (fun r=>(hfb r).1) hfg hsc hbound
  obtain ⟨hGG,hGe,hEx⟩:=bulk_marked_time_inputs (fun n=>M n+2) g v (Eventually.of_forall hv) hdF s hs K
    (fun j=>hK (s j)) μ hf
  let q:=boundedQuantile η
  let hq:=boundedQuantile_monotone η
  let F:=unitQuantileField q hq
  have hpair : (markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)=timeLaw.map q :=
    (boundedQuantile_law η).symm
  have hrpc:=cavityLabelMarkedLaw_tendsto_graph (markedTimeLaw K μ) q hq hpair hGG hGe hEx
    (continuousCavityProfile η B ha0 haK) (continuousCavityProfile_continuous η hB ha0 haK)
    (cavityTrueDiagonal ha0 haK)
  rw [hgraph] at hrpc
  refine ⟨⟨a,c,ha0,haK,haA,hc,hLa,hLc,hbound,hm.1,hrad,?_⟩⟩
  intro n d Λ hΛ
  have hprof j:=roundedCavityPair_conditions n d η hB ha0 haK j
  exact cavity_joint_array_recursion_limit n d (fun m=>M m+2) g v Λ hΛ K hK s hf
    (fun j=>(strictRoundModel F j).depth) (roundedCavityPair η B ha0 haK)
    (fun _=>cavityTrueDiagonal ha0 haK) (fun j=>stepCumulative (strictRoundModel F j).weight)
    (fun j=>(hprof j).1) (fun j=>(hprof j).2.1) (fun j=>(hprof j).2.2)
    (fun j=>stepCumulative_strictMono _ (strictRoundModel F j).weight_pos)
    (fun j=>stepCumulative_pos _ (strictRoundModel F j).weight_pos)
    (fun j=>stepCumulative_lt_one _ (strictRoundModel F j).weight_pos (strictRoundModel F j).weight_sum) hrpc
end SphericalPerceptronFreeEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data_oai := @OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data_oai
