-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:29:59.738586+00:00
-- url     : https://prove2.me/submissions/550125dc-4c8f-4bfd-a814-a80b0ac6a8c9

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_limit_geometry
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_limit_gg
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_marked_tangent_limit
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_quantile_marked_pair_reference_exists
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_quantile_pair_reference_exists

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

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

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

section GaussianField
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma tilt_mean_mulObservable {v F : S → ℝ} (c t : ℝ) :
    tiltMean μ v (fun x => c*F x) t = c * tiltMean μ v F t := by
  unfold tiltMean tiltIntegral
  simp_rw [show ∀ x, Real.exp (t*v x)*(c*F x) = c*(Real.exp (t*v x)*F x) by intro; ring]
  rw [integral_const_mul]
  ring

end GaussianField

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_ReweightedMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators Polynomial
namespace SphericalPerceptronFreeEnergy

lemma weighted_compact_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {a b : ℝ}
    (A : Ω → ℝ) (hA : Measurable A) (Z : Ω → Icc a b) (hZ : Measurable Z)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ x, |A x| ≤ C) (f : C(Icc a b,ℝ)) :
    Integrable (fun x => A x*f (Z x)) μ := by
  apply Integrable.of_bound (hA.mul (f.continuous.measurable.comp hZ)).aestronglyMeasurable (C*‖f‖)
  exact ae_of_all _ fun x => by
    change |A x*f (Z x)| ≤ C*‖f‖
    rw [abs_mul]
    exact mul_le_mul (hB x) (f.norm_coe_le_norm (Z x)) (abs_nonneg _) hC

lemma weighted_compact_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {a b : ℝ}
    (A : Ω → ℝ) (hA : Measurable A) (Z : Ω → Icc a b) (hZ : Measurable Z)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ x, |A x| ≤ C) (f g : C(Icc a b,ℝ)) :
    |(∫ x, A x*f (Z x) ∂μ)-(∫ x, A x*g (Z x) ∂μ)| ≤ C*‖f-g‖ := by
  rw [← integral_sub (weighted_compact_integrable μ A hA Z hZ C hC hB f)
    (weighted_compact_integrable μ A hA Z hZ C hC hB g)]
  have hb : ∀ x, ‖A x*f (Z x)-A x*g (Z x)‖ ≤ C*‖f-g‖ := fun x => by
    rw [←mul_sub,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hB x) ((f-g).norm_coe_le_norm (Z x)) (abs_nonneg _) hC
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hb)

lemma bounded_weighted_moment_limit {Ω : ℕ → Type*} {Ω' : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    (μ : (n : ℕ) → Measure (Ω n)) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν] {a b : ℝ}
    (A : (n : ℕ) → Ω n → ℝ) (A' : Ω' → ℝ)
    (Z : (n : ℕ) → Ω n → Icc a b) (Z' : Ω' → Icc a b)
    (hA : ∀ n, Measurable (A n)) (hA' : Measurable A')
    (hZ : ∀ n, Measurable (Z n)) (hZ' : Measurable Z')
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n x, |A n x| ≤ C) (hB' : ∀ x, |A' x| ≤ C)
    (hm : ∀ k : ℕ, Tendsto (fun n => ∫ x, A n x*(Z n x).val^k ∂μ n) atTop
      (𝓝 (∫ x, A' x*(Z' x).val^k ∂ν))) (f : C(Icc a b,ℝ)) :
    Tendsto (fun n => ∫ x, A n x*f (Z n x) ∂μ n) atTop
      (𝓝 (∫ x, A' x*f (Z' x) ∂ν)) := by
  have hpn (n : ℕ) (p : ℝ[X]) : Integrable (fun x => A n x*p.eval (Z n x).val) (μ n) :=
    weighted_compact_integrable (μ n) (A n) (hA n) (Z n) (hZ n) C hC (hB n) (p.toContinuousMapOn _)
  have hpl (p : ℝ[X]) : Integrable (fun x => A' x*p.eval (Z' x).val) ν :=
    weighted_compact_integrable ν A' hA' Z' hZ' C hC hB' (p.toContinuousMapOn _)
  have hp (p : ℝ[X]) : Tendsto (fun n => ∫ x, A n x*p.eval (Z n x).val ∂μ n) atTop
      (𝓝 (∫ x, A' x*p.eval (Z' x).val ∂ν)) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add,mul_add,integral_add (hpn _ p) (hpn _ q),
        integral_add (hpl p) (hpl q)] using hp.add hq
    | monomial k c =>
      simpa only [Polynomial.eval_monomial,mul_left_comm _ c,integral_const_mul]
        using (hm k).const_mul c
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε/(3*(C+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p,hpδ⟩ := exists_polynomial_near_continuousMap a b f δ hδ
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hp p) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h₁ := weighted_compact_error (μ n) (A n) (hA n) (Z n) (hZ n) C hC (hB n)
    (p.toContinuousMapOn _) f
  have h₂ := weighted_compact_error ν A' hA' Z' hZ' C hC hB' (p.toContinuousMapOn _) f
  have hsmall : C*‖p.toContinuousMapOn (Icc a b)-f‖ < ε/3 := by
    calc
      _ ≤ C*δ := mul_le_mul_of_nonneg_left hpδ.le hC
      _ < ε/3 := by dsimp [δ]; rw [← mul_div_assoc]; apply (div_lt_iff₀ (by positivity)).mpr; nlinarith
  have h₃ := hN n hn
  rw [Real.dist_eq] at h₃ ⊢
  have ht := abs_sub_le (∫ x, A n x*f (Z n x) ∂μ n)
    (∫ x, A n x*p.eval (Z n x).val ∂μ n) (∫ x, A' x*f (Z' x) ∂ν)
  have ht' := abs_sub_le (∫ x, A n x*p.eval (Z n x).val ∂μ n)
    (∫ x, A' x*p.eval (Z' x).val ∂ν) (∫ x, A' x*f (Z' x) ∂ν)
  simp only [Polynomial.toContinuousMapOn_apply,Polynomial.toContinuousMap_apply] at h₁ h₂
  rw [abs_sub_comm] at h₁
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TripleIndex
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

lemma ultrametric_triangle_small_eq {a b c : ℝ} (h : UltrametricTriangle a b c)
    (hab : a < b) : c = a := by
  have hlo : a ≤ c := by simpa only [min_eq_left hab.le] using h.1
  have hhi : c ≤ a := by
    rcases le_total b c with hbc | hcb
    · have : b ≤ a := by simpa only [min_eq_left hbc] using h.2.2
      exact (hab.not_ge this).elim
    · simpa only [min_eq_right hcb] using h.2.2
  exact le_antisymm hhi hlo

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

theorem weighted_kernel_homogeneous_eq_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] {D : X → ℝ} {K : X → X → ℝ} {B : ℝ}
    (hB : B < 1) (hD : ∀ᵐ r ∂μ, 0 < D r)
    (hK : ∀ r, Integrable (K r) μ) (hKpos : ∀ᵐ r ∂μ, ∀ᵐ s ∂μ, 0 ≤ K r s)
    (hrow : ∀ᵐ r ∂μ, (∫ s, K r s ∂μ) ≤ B * D r)
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hbounded : ∃ M : ℝ, ∀ᵐ r ∂μ, |f r| ≤ M)
    (heq : ∀ᵐ r ∂μ, f r * D r = ∫ s, K r s * f s ∂μ) :
    f =ᵐ[μ] 0 := by
  let C : ℝ := essSup (fun r => |f r|) μ
  obtain ⟨M, hM⟩ := hbounded
  have hb : IsBoundedUnder (· ≤ ·) (ae μ) (fun r => |f r|) :=
    isBoundedUnder_of_eventually_le hM
  have hcob : IsCoboundedUnder (· ≤ ·) (ae μ) (fun r => |f r|) :=
    isCoboundedUnder_le_of_le (ae μ) (fun r => abs_nonneg (f r))
  have hfC : ∀ᵐ r ∂μ, |f r| ≤ C := ae_le_essSup hb
  have hC : 0 ≤ C := by
    obtain ⟨r, hr⟩ := hfC.exists
    exact (abs_nonneg (f r)).trans hr
  have hsmall : ∀ᵐ r ∂μ, |f r| ≤ B * C := by
    filter_upwards [hD, hKpos, hrow, heq] with r hrD hrK hrrow hreq
    have hbound : ∀ᵐ s ∂μ, ‖K r s * f s‖ ≤ K r s * C := by
      filter_upwards [hrK, hfC] with s hsK hsC
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsK]
      exact mul_le_mul_of_nonneg_left hsC hsK
    have hi : Integrable (fun s => K r s * f s) μ :=
      ((hK r).mul_const C).mono' ((hK r).aestronglyMeasurable.mul hf) hbound
    have hh : |f r| * D r ≤ B * D r * C := by
      calc
        |f r| * D r = |f r * D r| := by rw [abs_mul, abs_of_pos hrD]
        _ = |∫ s, K r s * f s ∂μ| := by rw [hreq]
        _ ≤ ∫ s, ‖K r s * f s‖ ∂μ := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (fun s => K r s * f s) (μ := μ))
        _ ≤ ∫ s, K r s * C ∂μ :=
          integral_mono_ae hi.norm ((hK r).mul_const C) hbound
        _ = (∫ s, K r s ∂μ) * C := integral_mul_const C (K r)
        _ ≤ B * D r * C := mul_le_mul_of_nonneg_right hrrow hC
    nlinarith
  have hCC : C ≤ B * C := essSup_le_of_ae_le (B * C) hsmall hcob
  have hC0 : C = 0 := by nlinarith
  filter_upwards [hfC] with r hr
  exact abs_eq_zero.mp (le_antisymm (by simpa only [hC0] using hr) (abs_nonneg _))

lemma sphereKernel_nonneg (r s : Time) : 0 ≤ sphereKernel r s := by
  unfold sphereKernel
  rcases le_total (r : ℝ) (s : ℝ) with h | h
  · rw [min_eq_left h]
    nlinarith [r.property.1, s.property.2]
  · rw [min_eq_right h]
    nlinarith [s.property.1, r.property.2]

lemma sphereKernel_le_weight (r s : Time) :
    sphereKernel r s ≤ (r : ℝ) * (1 - max (r : ℝ) (s : ℝ)) := by
  unfold sphereKernel
  rcases le_total (r : ℝ) (s : ℝ) with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring_nf
    exact le_rfl
  · rw [min_eq_right h, max_eq_left h]
    nlinarith [r.property.2]

lemma sphereTail_integrable (μ : Measure Time) [IsFiniteMeasure μ] (r : Time) :
    Integrable (fun s : Time => 1 - max (r : ℝ) (s : ℝ)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    have := r.property.2
    have := s.property.2
    simp only [sub_nonneg, max_le_iff]
    exact ⟨‹_›, ‹_›⟩)]
  have h := r.property.1
  have hh : (r : ℝ) ≤ max (r : ℝ) (s : ℝ) := le_max_left _ _
  linarith

lemma sphereKernel_integrable (μ : Measure Time) [IsFiniteMeasure μ] (r : Time) :
    Integrable (sphereKernel r) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereKernel; fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereKernel_nonneg r s)]
  have h := sphereKernel_le_weight r s
  have hmax : 0 ≤ max (r : ℝ) (s : ℝ) := r.property.1.trans (le_max_left _ _)
  nlinarith [r.property.1, r.property.2]

lemma sphereTail_lower (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) {r : Time} (hr : (r : ℝ) ≤ B) :
    1 - B ≤ sphereTail μ r := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (sphereTail_integrable μ r) (by
      filter_upwards [hμ] with s hs
      exact sub_le_sub_left (max_le hr hs) 1)

lemma sphereKernel_row_bound (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} {r : Time} (hr : (r : ℝ) ≤ B) :
    (∫ s, sphereKernel r s ∂μ) ≤ B * sphereTail μ r := by
  have htail : 0 ≤ sphereTail μ r := integral_nonneg (fun s =>
    sub_nonneg.mpr (max_le r.property.2 s.property.2))
  calc
    _ ≤ ∫ s, (r : ℝ) * (1 - max (r : ℝ) (s : ℝ)) ∂μ :=
      integral_mono (sphereKernel_integrable μ r) ((sphereTail_integrable μ r).const_mul _)
        (sphereKernel_le_weight r)
    _ = (r : ℝ) * sphereTail μ r := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hr htail

theorem sphere_equation_unique (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B)
    {a b : Time → ℝ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (haBound : ∃ C : ℝ, ∀ᵐ r ∂μ, |a r| ≤ C)
    (hbBound : ∃ C : ℝ, ∀ᵐ r ∂μ, |b r| ≤ C)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ)
    (hbEq : ∀ᵐ r ∂μ, b r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * b s ∂μ) :
    a =ᵐ[μ] b := by
  obtain ⟨A, hA⟩ := haBound
  obtain ⟨B', hB'⟩ := hbBound
  have hzero : (fun r => a r - b r) =ᵐ[μ] 0 :=
    weighted_kernel_homogeneous_eq_zero μ (D := sphereTail μ) (K := sphereKernel) hB
      (by filter_upwards [hμ] with r hr; have := sphereTail_lower μ hμ hr; linarith)
      (sphereKernel_integrable μ)
      (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall (sphereKernel_nonneg r))
      (by filter_upwards [hμ] with r hr; exact sphereKernel_row_bound μ hr)
      (ha.sub hb)
      ⟨A + B', by
        filter_upwards [hA, hB'] with r hAr hBr
        exact (abs_sub (a r) (b r)).trans (add_le_add hAr hBr)⟩
      (by
        filter_upwards [haEq, hbEq] with r har hbr
        have hai : Integrable (fun s => sphereKernel r s * a s) μ := by
          apply ((sphereKernel_integrable μ r).mul_const A).mono'
            ((sphereKernel_integrable μ r).aestronglyMeasurable.mul ha)
          filter_upwards [hA] with s hs
          change |sphereKernel r s * _| ≤ _
          rw [abs_mul, abs_of_nonneg (sphereKernel_nonneg r s)]
          exact mul_le_mul_of_nonneg_left hs (sphereKernel_nonneg r s)
        have hbi : Integrable (fun s => sphereKernel r s * b s) μ := by
          apply ((sphereKernel_integrable μ r).mul_const B').mono'
            ((sphereKernel_integrable μ r).aestronglyMeasurable.mul hb)
          filter_upwards [hB'] with s hs
          change |sphereKernel r s * _| ≤ _
          rw [abs_mul, abs_of_nonneg (sphereKernel_nonneg r s)]
          exact mul_le_mul_of_nonneg_left hs (sphereKernel_nonneg r s)
        simp_rw [mul_sub]
        rw [integral_sub hai hbi, sub_mul, har, hbr]
        ring)
  filter_upwards [hzero] with r hr
  exact sub_eq_zero.mp hr

lemma sphereTail_nonneg (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    0 ≤ sphereTail μ r := integral_nonneg (fun s =>
      sub_nonneg.mpr (max_le r.property.2 s.property.2))

lemma sphereTail_upper (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    sphereTail μ r ≤ 1 - (r : ℝ) := by
  calc
    _ ≤ ∫ _ : Time, 1 - (r : ℝ) ∂μ :=
      integral_mono (sphereTail_integrable μ r) (integrable_const _)
        (fun s => sub_le_sub_left (le_max_left _ _) 1)
    _ = _ := by simp

theorem sphere_equation_support_bound (μ : Measure Time) [IsProbabilityMeasure μ]
    {a : Time → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (haNonneg : ∀ᵐ r ∂μ, 0 ≤ a r) (haBound : ∀ᵐ r ∂μ, a r ≤ A)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ) :
    ∀ᵐ r : Time ∂μ, (r : ℝ) ≤ A / (1 + A) := by
  filter_upwards [haBound, haEq] with r har heq
  have hint : 0 ≤ ∫ s, sphereKernel r s * a s ∂μ :=
    integral_nonneg_of_ae (by
      filter_upwards [haNonneg] with s hs
      exact mul_nonneg (sphereKernel_nonneg r s) hs)
  have hineq : (r : ℝ) ≤ A * (1 - (r : ℝ)) := by
    calc
      _ ≤ a r * sphereTail μ r := by linarith
      _ ≤ A * sphereTail μ r := mul_le_mul_of_nonneg_right har (sphereTail_nonneg μ r)
      _ ≤ _ := mul_le_mul_of_nonneg_left (sphereTail_upper μ r) hA
  apply (le_div_iff₀ (by linarith : 0 < 1 + A)).mpr
  nlinarith

lemma hasDerivWithinAt_max_right (x s : ℝ) :
    HasDerivWithinAt (fun y => max y s) (if s ≤ x then 1 else 0) (Ioi x) x := by
  split_ifs with h
  · exact (hasDerivAt_id x).hasDerivWithinAt.congr
      (fun y hy => max_eq_left (h.trans (le_of_lt hy))) (max_eq_left h)
  · have hd : HasDerivAt (fun y => max y s) 0 x := by
      apply (hasDerivAt_const x s).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds (lt_of_not_ge h)] with y hy
      exact max_eq_right (le_of_lt hy)
    exact hd.hasDerivWithinAt

lemma realTail_right_derivative (μ : Measure Time) [IsFiniteMeasure μ] (x : ℝ) :
    HasDerivWithinAt (realTail μ) (-realCDF μ x) (Ioi x) x := by
  have hlim (s : Time) :
      Tendsto (slope (fun y => 1 - max y (s : ℝ)) x) (𝓝[Ioi x] x)
        (𝓝 (-(if (s : ℝ) ≤ x then 1 else 0))) := by
    have hd := (hasDerivAt_const x (1 : ℝ)).hasDerivWithinAt.sub
      (hasDerivWithinAt_max_right x (s : ℝ))
    change HasDerivWithinAt (fun y => 1 - max y (s : ℝ))
      (0 - (if (s : ℝ) ≤ x then 1 else 0)) (Ioi x) x at hd
    have hh := hasDerivWithinAt_iff_tendsto_slope.mp hd
    simpa using hh
  have hint : (∫ s : Time, -(if (s : ℝ) ≤ x then 1 else 0) ∂μ) = -realCDF μ x := by
    rw [integral_neg]
    congr 1
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ x}.indicator (fun _ => (1 : ℝ)) s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    simp [realCDF]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hd := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun y (s : Time) => slope (fun z => 1 - max z (s : ℝ)) x y)
    (fun _ => (1 : ℝ))
    (Eventually.of_forall fun y => by unfold slope; fun_prop)
    (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      filter_upwards [] with s
      rw [slope_def_field, Real.norm_eq_abs, abs_div]
      have h := abs_max_sub_max_le_max y (s : ℝ) x (s : ℝ)
      simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (y - x))] at h
      have he : |(1 - max y (s : ℝ)) - (1 - max x (s : ℝ))| =
          |max y (s : ℝ) - max x (s : ℝ)| := by
        rw [show (1 - max y (s : ℝ)) - (1 - max x (s : ℝ)) =
          -(max y (s : ℝ) - max x (s : ℝ)) by ring, abs_neg]
      rw [he]
      exact (div_le_one (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hy)))).mpr h)
    (integrable_const _) (Eventually.of_forall hlim)
  rw [hint] at hd
  convert hd using 1
  · ext y
    rw [slope_def_field, realTail, realTail, ← integral_sub (realTail_integrable μ y)
    (realTail_integrable μ x), ← integral_div]
    simp only [slope_def_field]
  · simp

lemma realCDF_monotone (μ : Measure Time) [IsFiniteMeasure μ] :
    Monotone (realCDF μ) := by
  intro x y hxy
  exact measureReal_mono (fun _ hs => hs.trans hxy)

lemma realCDF_integrable (μ : Measure Time) [IsFiniteMeasure μ] (a b : ℝ) :
    IntervalIntegrable (realCDF μ) volume a b :=
  (realCDF_monotone μ).intervalIntegrable

lemma integral_cdf_mul (μ : Measure Time) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 r) :
    (∫ t in 0..r, realCDF μ t * f t) =
      ∫ s : Time, if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, f t else 0 ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 r)
  have hfi : Integrable f ν := (intervalIntegrable_iff_integrableOn_Icc_of_le hr).mp hf
  have hmeas : MeasurableSet {p : ℝ × Time | (p.2 : ℝ) ≤ p.1} :=
    measurableSet_le (by fun_prop) measurable_fst
  have hbase : Integrable (fun p : ℝ × Time => f p.1) (ν.prod μ) := by
    simpa using hfi.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hswap := integral_integral_swap (μ := ν) (ν := μ)
    (f := fun t s => {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator (fun p => f p.1) (t, s))
    (hbase.indicator hmeas)
  have hleft (t : ℝ) :
      (∫ s : Time, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => f p.1) (t, s) ∂μ) = realCDF μ t * f t := by
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ t}.indicator (fun _ => f t) s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    simp [realCDF]
  have hright (s : Time) :
      (∫ t, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => f p.1) (t, s) ∂ν) =
        if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, f t else 0 := by
    change (∫ t, (Ici (s : ℝ)).indicator f t ∂ν) = _
    rw [integral_indicator measurableSet_Ici]
    have hset : Icc 0 r ∩ Ici (s : ℝ) = Icc (s : ℝ) r := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · intro h; exact ⟨h.2, h.1.2⟩
      · intro h; exact ⟨⟨s.property.1.trans h.1, h.2⟩, h.1⟩
    dsimp only [ν]
    rw [Measure.restrict_restrict measurableSet_Ici, inter_comm, hset]
    split_ifs with hs
    · rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs]
    · simp [Icc_eq_empty_of_lt (lt_of_not_ge hs)]
  have hl : (∫ (t : ℝ), realCDF μ t * f t ∂ν) = ∫ t in 0..r, realCDF μ t * f t := by
    dsimp only [ν]
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr]
  simpa only [Function.uncurry_apply_pair, hleft, hright, hl] using hswap

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

lemma realTail_inv_integral (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    (realTail μ r)⁻¹ - (realTail μ 0)⁻¹ =
      ∫ t in 0..r, realCDF μ t * cappedDensity μ B t := by
  have hn (x : ℝ) (hx : x ≤ B) : realTail μ x ≠ 0 :=
    ne_of_gt ((sub_pos.mpr hB).trans_le (realTail_lower μ hμ hx))
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := fun x : ℝ => (realTail μ x)⁻¹) hr
  · exact (realTail_continuous μ).continuousOn.inv₀ (fun x hx => hn x (hx.2.trans hrB))
  · intro x hx
    have hd := (realTail_right_derivative μ x).inv (hn x (hx.2.le.trans hrB))
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [cappedDensity_eq μ hμ (hx.2.le.trans hrB), neg_neg, div_eq_mul_inv, inv_pow]
  · exact (realCDF_integrable μ 0 r).mul_continuousOn
      (cappedDensity_continuous μ hB).continuousOn

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

lemma weightedCDF_fubini (μ : Measure Time) [IsFiniteMeasure μ]
    {a : Time → ℝ} (ha : Integrable a μ) {r : ℝ} (hr : 0 ≤ r) :
    IntervalIntegrable (weightedCDF μ a) volume 0 r ∧
    (∫ t in 0..r, weightedCDF μ a t) = ∫ s : Time, max (r - s) 0 * a s ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 r)
  have hmeas : MeasurableSet {p : ℝ × Time | (p.2 : ℝ) ≤ p.1} :=
    measurableSet_le (by fun_prop) measurable_fst
  have hbase : Integrable (fun p : ℝ × Time => a p.2) (ν.prod μ) := by
    simpa using (integrable_const (1 : ℝ) (μ := ν)).mul_prod ha
  have hi := hbase.indicator hmeas
  have hleft (t : ℝ) :
      (∫ s : Time, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => a p.2) (t, s) ∂μ) = weightedCDF μ a t := by
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ t}.indicator a s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    rfl
  have hright (s : Time) :
      (∫ t, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => a p.2) (t, s) ∂ν) = max (r - s) 0 * a s := by
    change (∫ t, (Ici (s : ℝ)).indicator (fun _ => a s) t ∂ν) = _
    rw [integral_indicator measurableSet_Ici]
    have hset : Icc 0 r ∩ Ici (s : ℝ) = Icc (s : ℝ) r := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · intro h; exact ⟨h.2, h.1.2⟩
      · intro h; exact ⟨⟨s.property.1.trans h.1, h.2⟩, h.1⟩
    dsimp only [ν]
    rw [Measure.restrict_restrict measurableSet_Ici, inter_comm, hset,
      setIntegral_const]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal', smul_eq_mul]
  have hl : (∫ t, weightedCDF μ a t ∂ν) = ∫ t in 0..r, weightedCDF μ a t := by
    dsimp only [ν]
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr]
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hr).mpr
    have hi' : Integrable (weightedCDF μ a) ν := by
      simpa only [Function.uncurry_apply_pair, hleft] using hi.integral_prod_left
    change Integrable (weightedCDF μ a) ν
    exact hi'
  · have hs := integral_integral_swap (μ := ν) (ν := μ)
      (f := fun t s => {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator (fun p => a p.2) (t,s)) hi
    simpa only [Function.uncurry_apply_pair, hleft, hright, hl] using hs

lemma realTail_inv_formula (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    (realTail μ r)⁻¹ - (realTail μ 0)⁻¹ =
      realCDF μ r * cappedA μ B r - weightedCDF μ (fun s => cappedA μ B s) r := by
  rw [realTail_inv_integral μ hB hμ hr hrB,
    integral_cdf_mul μ hr ((cappedDensity_continuous μ hB).intervalIntegrable 0 r)]
  have hm : MeasurableSet {s : Time | (s : ℝ) ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hA : Integrable (fun s : Time => cappedA μ B s) μ :=
    continuous_time_integrable μ ((cappedA_continuous μ hB).comp continuous_subtype_val)
  have he (s : Time) :
      (if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, cappedDensity μ B t else 0) =
      {s : Time | (s : ℝ) ≤ r}.indicator (fun _ => cappedA μ B r) s -
      {s : Time | (s : ℝ) ≤ r}.indicator (fun s => cappedA μ B s) s := by
    by_cases hs : (s : ℝ) ≤ r
    · simp only [hs, ite_true, mem_ofPred_eq, indicator_of_mem]
      have h := intervalIntegral.integral_add_adjacent_intervals
        ((cappedDensity_continuous μ hB).intervalIntegrable (μ := volume) 0 (s : ℝ))
        ((cappedDensity_continuous μ hB).intervalIntegrable (μ := volume) (s : ℝ) r)
      change _ = _ - _
      exact eq_sub_of_add_eq' h
    · simp [hs]
  simp_rw [he]
  rw [integral_sub ((integrable_const _).indicator hm) (hA.indicator hm),
    integral_indicator_const _ hm, integral_indicator hm]
  rfl

lemma realTail_mul_A (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    realTail μ r * cappedA μ B r = r * (realTail μ 0)⁻¹ -
      ∫ s : Time, max (r - s) 0 * cappedA μ B s ∂μ := by
  have hA := cappedA_continuous μ hB
  have hAi : Integrable (fun s : Time => cappedA μ B s) μ :=
    continuous_time_integrable μ (hA.comp continuous_subtype_val)
  have hG := weightedCDF_fubini μ hAi hr
  have hd (x : ℝ) (hx : x ∈ Ioo 0 r) :
      HasDerivWithinAt (fun t => realTail μ t * cappedA μ B t)
        ((realTail μ 0)⁻¹ - weightedCDF μ (fun s => cappedA μ B s) x) (Ioi x) x := by
    have hn : realTail μ x ≠ 0 :=
      ne_of_gt ((sub_pos.mpr hB).trans_le (realTail_lower μ hμ (hx.2.le.trans hrB)))
    have he := realTail_inv_formula μ hB hμ hx.1.le (hx.2.le.trans hrB)
    have hp := (realTail_right_derivative μ x).mul (cappedA_hasDerivAt μ hB x).hasDerivWithinAt
    convert! hp using 1
    all_goals try with_reducible_and_instances rfl
    rw [cappedDensity_eq μ hμ (hx.2.le.trans hrB)]
    have hm : realTail μ x * ((realTail μ x)⁻¹ ^ 2) = (realTail μ x)⁻¹ := by
      field_simp
    rw [hm]
    linarith
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := fun t => realTail μ t * cappedA μ B t)
    (f' := fun t => (realTail μ 0)⁻¹ - weightedCDF μ (fun s => cappedA μ B s) t)
    hr ((realTail_continuous μ).mul hA).continuousOn hd
    (intervalIntegrable_const.sub hG.1)
  rw [intervalIntegral.integral_sub (f := fun _ => (realTail μ 0)⁻¹)
    intervalIntegrable_const hG.1, hG.2] at h
  simpa using h.symm

lemma realTail_at_top (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) : realTail μ B = 1 - B := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := integral_congr_ae (by
      filter_upwards [hμ] with s hs
      rw [max_eq_left hs])
    _ = _ := by simp

lemma realCDF_at_top (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) : realCDF μ B = 1 := by
  unfold realCDF Measure.real
  have h : {s : Time | (s : ℝ) ≤ B} =ᵐ[μ] univ := by
    filter_upwards [hμ] with s hs
    change ((s : ℝ) ≤ B) = True
    simp [hs]
  rw [measure_congr h]
  simp

lemma weightedCDF_at_top (μ : Measure Time) {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (a : Time → ℝ) :
    weightedCDF μ a B = ∫ s, a s ∂μ := by
  unfold weightedCDF
  have h : {s : Time | (s : ℝ) ≤ B} =ᵐ[μ] univ := by
    filter_upwards [hμ] with s hs
    change ((s : ℝ) ≤ B) = True
    simp [hs]
  rw [setIntegral_congr_set h, setIntegral_univ]

lemma realTail_inv_zero_formula (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hB : B < 1) (hB0 : 0 ≤ B) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) :
    (realTail μ 0)⁻¹ = 1 + ∫ s : Time, (1 - (s : ℝ)) * cappedA μ B s ∂μ := by
  have hA : Continuous (fun s : Time => cappedA μ B s) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  have hAi := continuous_time_integrable μ hA
  have hSAi : Integrable (fun s : Time => (s : ℝ) * cappedA μ B s) μ :=
    continuous_time_integrable μ (continuous_subtype_val.mul hA)
  have htop := realTail_inv_formula μ hB hμ hB0 le_rfl
  rw [realTail_at_top μ hμ, realCDF_at_top μ hμ, one_mul,
    weightedCDF_at_top μ hμ] at htop
  have hproduct := realTail_mul_A μ hB hμ hB0 le_rfl
  rw [realTail_at_top μ hμ] at hproduct
  have hi : (∫ s : Time, max (B - s) 0 * cappedA μ B s ∂μ) =
      B * (∫ s : Time, cappedA μ B s ∂μ) - ∫ s : Time, (s : ℝ) * cappedA μ B s ∂μ := by
    calc
      _ = ∫ s : Time, B * cappedA μ B s - (s : ℝ) * cappedA μ B s ∂μ :=
        integral_congr_ae (by
          filter_upwards [hμ] with s hs
          rw [max_eq_left (sub_nonneg.mpr hs)]
          ring)
      _ = _ := by rw [integral_sub (hAi.const_mul B) hSAi, integral_const_mul]
  rw [hi] at hproduct
  have hc : (realTail μ 0)⁻¹ = 1 + (∫ s : Time, cappedA μ B s ∂μ) -
      ∫ s : Time, (s : ℝ) * cappedA μ B s ∂μ := by
    have htop' := congrArg (fun z : ℝ => (1 - B) * z) htop
    have hinv : (1 - B) * (1 - B)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hB))
    nlinarith
  rw [hc]
  have hi' : (∫ s : Time, (1 - (s : ℝ)) * cappedA μ B s ∂μ) =
      (∫ s : Time, cappedA μ B s ∂μ) - ∫ s : Time, (s : ℝ) * cappedA μ B s ∂μ := by
    simp_rw [sub_mul, one_mul]
    exact integral_sub hAi hSAi
  rw [hi']
  ring

theorem cappedA_sphere_equation (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    cappedA μ B r * realTail μ r = r +
      ∫ s : Time, (min r (s : ℝ) - r * (s : ℝ)) * cappedA μ B s ∂μ := by
  have hA : Continuous (fun s : Time => cappedA μ B s) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  have ht := realTail_mul_A μ hB hμ hr hrB
  rw [realTail_inv_zero_formula μ hB (hr.trans hrB) hμ] at ht
  have hk (s : Time) :
      (min r (s : ℝ) - r * (s : ℝ)) * cappedA μ B s =
      r * ((1 - (s : ℝ)) * cappedA μ B s) - max (r - s) 0 * cappedA μ B s := by
    rcases le_total r (s : ℝ) with hs | hs
    · rw [min_eq_left hs, max_eq_right (sub_nonpos.mpr hs)]
      ring
    · rw [min_eq_right hs, max_eq_left (sub_nonneg.mpr hs)]
      ring
  simp_rw [hk]
  rw [integral_sub (continuous_time_integrable μ (by fun_prop))
    (continuous_time_integrable μ (by fun_prop)), integral_const_mul]
  nlinarith [ht]

lemma cappedA_eq_integral (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    cappedA μ B r = ∫ t in 0..r, (realTail μ t)⁻¹ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hr] at hx
  exact cappedDensity_eq μ hμ (hx.2.trans hrB)

theorem sphere_self_consistency (μ : Measure Time) [IsProbabilityMeasure μ]
    {a : Time → ℝ} {A : ℝ} (hA : 0 ≤ A) (ha : AEStronglyMeasurable a μ)
    (haNonneg : ∀ᵐ r ∂μ, 0 ≤ a r) (haBound : ∀ᵐ r ∂μ, a r ≤ A)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ) :
    (∀ᵐ r : Time ∂μ, a r = ∫ t in 0..(r : ℝ), (realTail μ t)⁻¹ ^ 2) ∧
      ∀ᵐ r : Time ∂μ, (r : ℝ) ≤ A / (1 + A) := by
  have hμ := sphere_equation_support_bound μ hA haNonneg haBound haEq
  have hB : A / (1 + A) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let B := A / (1 + A)
  have hb : Continuous (fun s : Time => cappedA μ B s) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  obtain ⟨C, hC⟩ := (isCompact_range hb.abs).bddAbove
  have hident := sphere_equation_unique μ hB hμ ha hb.aestronglyMeasurable
    ⟨A, by
      filter_upwards [haNonneg, haBound] with s hs hsA
      simpa only [abs_of_nonneg hs] using hsA⟩
    ⟨C, Eventually.of_forall fun s => hC (mem_range_self s)⟩ haEq
    (by
      filter_upwards [hμ] with r hr
      exact cappedA_sphere_equation μ hB hμ r.property.1 hr)
  refine ⟨?_, hμ⟩
  filter_upwards [hident, hμ] with r hr hrB
  rw [hr, cappedA_eq_integral μ hμ r.property.1 hrB]

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_adjoint_basis (v : ι → E) (i : ι) :
    (gaussianRows v).adjoint (EuclideanSpace.basisFun ι ℝ i) = v i := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, gaussianRows_apply,real_inner_comm]

lemma gaussianRows_map_stdGaussian (v : ι → E) :
    (stdGaussian E).map (gaussianRows v) = multivariateGaussian 0 (Matrix.gram ℝ v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  simp only [ContinuousLinearMap.toBilinForm_apply,OrthonormalBasis.coe_toBasis]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,gaussianRows_adjoint_basis,
    gaussianRows_adjoint_basis,covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simp
  rfl

end GaussianRows

lemma gaussianReplicaTest_apply {ι : Type*} [Fintype ι] (f : ℝ →ᵇ ℝ) (z : EuclideanSpace ℝ ι) :
    gaussianReplicaTest f z = ∏ i, f (z i) := by simp [gaussianReplicaTest]

open TopologicalSpace

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

omit [IsProbabilityMeasure μ] in
lemma replicaMean_const_mul {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ} (c : ℝ) :
    gibbsReplicaMean μ H n (fun x => c*G x) = c*gibbsReplicaMean μ H n G :=
  tilt_mean_mulObservable _ c 1

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

lemma gibbsReplicaMean_product_of_integrable {H F : S → ℝ} {n : ℕ}
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hF : Measurable F) (hG : Measurable G)
    (hi : Integrable (fun x => Real.exp (H x)) μ) {D B : ℝ}
    (hFD : ∀ x, |F x| ≤ D) (hGB : ∀ x, |G x| ≤ B) :
    gibbsReplicaMean μ H (n+1) (fun x => F (x 0)*G (fun j => x j.succ)) =
      tiltMean μ H F 1*gibbsReplicaMean μ H n G := by
  have heI : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ heI
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  rw [← tilt_law_integral_of_integrable μ hH heI]
  let ν := tiltLaw μ H 1
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm
  rw [← he.integral_comp' (fun x => F (x 0)*G (fun j => x j.succ))]
  change (∫ p : S×(Fin n → S), F ((Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) 0)*
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
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_prefix_integral (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) ∂P := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val)) :=
    hG.comp (by fun_prop)
  have hi : Integrable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using hGB (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => kernelInfiniteReplica_prefix_integral _ a r hG

lemma annealedInfiniteReplica_gibbs_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P := by
  rw [annealedInfiniteReplica_prefix_integral κ P H hH r hG hGB]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r G

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
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_GibbsOverlapArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {A S K : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [CompactSpace K]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))
variable (Q : S → S → K) (hQ : Measurable (Function.uncurry Q))

omit [TopologicalSpace K] [BorelSpace K] [SecondCountableTopology K] [CompactSpace K] in
lemma gibbsOverlapArray_integral {F : CompactArray K → ℝ} (hF : Measurable F) :
    (∫ R, F R ∂gibbsOverlapArrayLaw κ P H hH Q hQ) =
      ∫ a, F (overlapArray Q a.2) ∂annealedInfiniteReplicaMeasure κ P H hH :=
  integral_map ((overlapArray_measurable Q hQ).comp measurable_snd).aemeasurable hF.aestronglyMeasurable

omit [CompactSpace K]

lemma gibbsOverlapArray_block (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ)
    (F : CompactBlock K r →ᵇ ℝ) :
    (∫ R, F (compactBlock r R) ∂gibbsOverlapArrayLaw κ P H hH Q hQ) =
      ∫ a, gibbsReplicaMean (κ a) (H a) r
        (fun x => F (fun i j => Q (x i) (x j))) ∂P := by
  rw [gibbsOverlapArray_integral κ P H hH Q hQ
    (F:=fun R => F (compactBlock r R)) (F.continuous.measurable.comp (compactBlock_continuous r).measurable)]
  exact annealedInfiniteReplica_gibbs_prefix κ P H hH hexp r
    (F.continuous.measurable.comp (Measurable.of_eval fun row => Measurable.of_eval fun column =>
      hQ.comp ((measurable_pi_apply row).prodMk (measurable_pi_apply column))))
    (fun x => by
      change |F (fun i j => Q (x i) (x j))|≤‖F‖
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (fun i j => Q (x i) (x j)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkModel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma bulkGibbsArray_block (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) :
    (∫ R, F (compactBlock r R) ∂bulkGibbsArrayLaw n M f v) =
      ∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r
        (fun x => F (fun i j => bulkOverlap (x i) (x j))) ∂bulkDisorderLaw (n+1) M := by
  exact gibbsOverlapArray_block (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous (n+1) M f v).measurable _ (bulkOverlap_measurable (n+1))
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f v)) r F

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMarkedKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma freshMarkedMatrixKernel_gram {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin r→E) :
    freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v)=
      ∫ z, Ψ z ∂multivariateGaussian 0 (Matrix.gram ℝ v) :=
  (Classical.choose_spec (freshMarked_extension_exists Ψ)).2 (gramCovariance v)

lemma freshMarkedMatrixKernel_gaussian {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (v : Fin r→E) :
    (∫ g, Ψ (gaussianRows v g) ∂stdGaussian E) = freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v) := by
  rw [freshMarkedMatrixKernel_gram,←gaussianRows_map_stdGaussian v,
    integral_map (gaussianRows v).continuous.measurable.aemeasurable Ψ.continuous.aestronglyMeasurable]

lemma freshMarkedMatrixKernel_two {r : ℕ} (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (v : Fin r→E) :
    (∫ g, Ψ (gaussianRows v g.1)*Φ (gaussianRows v g.2)
      ∂(stdGaussian E).prod (stdGaussian E)) =
      freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v)*freshMarkedMatrixKernel Φ (Matrix.gram ℝ v) := by
  rw [integral_prod_mul (fun g => Ψ (gaussianRows v g)) (fun g => Φ (gaussianRows v g))]
  rw [freshMarkedMatrixKernel_gaussian,freshMarkedMatrixKernel_gaussian]

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

lemma twoFreshReplica_fubini {r : ℕ} (ν : Measure (Fin r→S)) [IsProbabilityMeasure ν]
    (v : S→E) (hv : Continuous v) (G : (Fin r→S)→ℝ) (hG : Measurable G)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |G x|≤C)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    (∫ g, ∫ x, G x*Ψ (gaussianRows (fun i => v (x i)) g.1)*
      Φ (gaussianRows (fun i => v (x i)) g.2) ∂ν
      ∂(stdGaussian E).prod (stdGaussian E)) =
    ∫ x, G x*freshMarkedMatrixKernel Ψ (Matrix.gram ℝ (fun i => v (x i)))*
      freshMarkedMatrixKernel Φ (Matrix.gram ℝ (fun i => v (x i))) ∂ν := by
  let P := (stdGaussian E).prod (stdGaussian E)
  have hc₁ : Continuous (fun p : (E×E)×(Fin r→S) =>
      Ψ (gaussianRows (fun i => v (p.2 i)) p.1.1)) :=
    Ψ.continuous.comp ((gaussianRows_joint_continuous (r:=r) hv).comp
      (continuous_fst.fst.prodMk continuous_snd))
  have hc₂ : Continuous (fun p : (E×E)×(Fin r→S) =>
      Φ (gaussianRows (fun i => v (p.2 i)) p.1.2)) :=
    Φ.continuous.comp ((gaussianRows_joint_continuous (r:=r) hv).comp
      (continuous_fst.snd.prodMk continuous_snd))
  have hm : Measurable (fun p : (E×E)×(Fin r→S) => G p.2*
      Ψ (gaussianRows (fun i => v (p.2 i)) p.1.1)*Φ (gaussianRows (fun i => v (p.2 i)) p.1.2)) :=
    ((hG.comp measurable_snd).mul hc₁.measurable).mul hc₂.measurable
  have hi : Integrable (fun p : (E×E)×(Fin r→S) => G p.2*
      Ψ (gaussianRows (fun i => v (p.2 i)) p.1.1)*Φ (gaussianRows (fun i => v (p.2 i)) p.1.2))
      (P.prod ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (C*‖Ψ‖*‖Φ‖)
    exact ae_of_all _ fun p => by
      simp only [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (mul_le_mul (hb _) (Ψ.norm_coe_le_norm _) (abs_nonneg _) hC)
        (Φ.norm_coe_le_norm _) (abs_nonneg _) (mul_nonneg hC (norm_nonneg _))
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp_rw [mul_assoc]
    rw [integral_const_mul,freshMarkedMatrixKernel_two]

lemma gibbs_twoFreshReplica_fubini {r : ℕ} (μ : Measure S) [IsProbabilityMeasure μ]
    {H : S→ℝ} (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (v : S→E) (hv : Continuous v) (G : (Fin r→S)→ℝ) (hG : Measurable G)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |G x|≤C)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    (∫ g, gibbsReplicaMean μ H r (fun x => G x*Ψ (gaussianRows (fun i => v (x i)) g.1)*
      Φ (gaussianRows (fun i => v (x i)) g.2)) ∂(stdGaussian E).prod (stdGaussian E)) =
    gibbsReplicaMean μ H r (fun x => G x*freshMarkedMatrixKernel Ψ (Matrix.gram ℝ (fun i => v (x i)))*
      freshMarkedMatrixKernel Φ (Matrix.gram ℝ (fun i => v (x i)))) := by
  let := tilt_law_probability_of_integrable μ (by simpa only [one_mul] using hi :
    Integrable (fun x => Real.exp (1*H x)) μ)
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  exact twoFreshReplica_fubini _ v hv G hG hC hb Ψ Φ
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedMoments
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

lemma freshMarkedCompactBlockKernel_spin {N r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r)→ᵇℝ)
    (x : Fin r→NormalizedSpin N) :
    freshMarkedCompactBlockKernel Ψ (fun i j => bulkOverlap (x i) (x j)) =
      freshMarkedMatrixKernel Ψ (Matrix.gram ℝ (fun i => (x i).val)) := rfl

lemma bulk_twoFresh_block (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : CompactBlock CompactOverlap r→ᵇℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r)→ᵇℝ) :
    (∫ a, ∫ z, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) r
      (fun x => F (fun i j => bulkOverlap (x i) (x j))*
        Ψ (gaussianRows (fun i => (x i).val) z.1)*Φ (gaussianRows (fun i => (x i).val) z.2))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin (n+1)))).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1))))
      ∂bulkDisorderLaw (n+1) M) =
    ∫ Q, (F*freshMarkedCompactBlockKernel Ψ*freshMarkedCompactBlockKernel Φ) (compactBlock r Q)
      ∂bulkGibbsArrayLaw n M f v := by
  rw [bulkGibbsArray_block]
  apply integral_congr_ae
  refine ae_of_all _ fun a => ?_
  have hc : Continuous (fun x : Fin r→NormalizedSpin (n+1) => F (fun i j => bulkOverlap (x i) (x j))) := by
    apply F.continuous.comp
    unfold bulkOverlap spinOverlap
    fun_prop
  have hG := hc.measurable
  have h := gibbs_twoFreshReplica_fubini (unitSphereLaw (n+1))
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v a) (fun x : NormalizedSpin (n+1) => x.val)
    continuous_subtype_val (fun x => F (fun i j => bulkOverlap (x i) (x j))) hG
    (norm_nonneg F) (fun x => F.norm_coe_le_norm _) Ψ Φ
  simpa only [Function.comp_def,id_eq,BoundedContinuousFunction.mul_apply,freshMarkedCompactBlockKernel_spin] using h

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RestorationMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S]

lemma restorationReplicaTest_measurable (r : ℕ) {W : S→ℝ} {F : (Fin r→S)→ℝ}
    (hW : Measurable W) (hF : Measurable F) (k : ℕ) :
    Measurable (restorationReplicaTest r W F k) := by
  induction k with
  | zero => exact hF
  | succ k hk =>
    exact (hW.comp (measurable_pi_apply 0)).mul
      (hk.comp (Measurable.of_eval fun index => measurable_pi_apply index.succ))

omit [MeasurableSpace S] in
lemma restorationReplicaTest_bound (r : ℕ) {W : S→ℝ} {F : (Fin r→S)→ℝ}
    {D B : ℝ} (hD : 0≤D) (_hB : 0≤B) (hW : ∀ x, |W x|≤D) (hF : ∀ x, |F x|≤B)
    (k : ℕ) (x : Fin (r+k)→S) : |restorationReplicaTest r W F k x| ≤ D^k*B := by
  induction k with
  | zero => simpa only [restorationReplicaTest,pow_zero,one_mul] using hF x
  | succ k hk =>
    rw [restorationReplicaTest,abs_mul]
    exact (mul_le_mul (hW _) (hk _) (abs_nonneg _) hD).trans_eq (by ring)

lemma restoration_replica_moment (μ : Measure S) [IsProbabilityMeasure μ]
    {H W : S→ℝ} {r : ℕ} {F : (Fin r→S)→ℝ}
    (hH : Measurable H) (hW : Measurable W) (hF : Measurable F)
    (hi : Integrable (fun x => Real.exp (H x)) μ)
    {D B : ℝ} (hD : 0≤D) (hB : 0≤B) (hWD : ∀ x, |W x|≤D) (hFB : ∀ x, |F x|≤B)
    (k : ℕ) :
    gibbsReplicaMean μ H (r+k) (restorationReplicaTest r W F k) =
      (tiltMean μ H W 1)^k*gibbsReplicaMean μ H r F := by
  induction k with
  | zero => simp only [restorationReplicaTest,pow_zero,one_mul,Nat.add_zero]
  | succ k hk =>
    change gibbsReplicaMean μ H ((r+k)+1) (fun x => W (x 0)*restorationReplicaTest r W F k (fun i => x i.succ)) = _
    rw [gibbsReplicaMean_product_of_integrable μ hH hW
        (restorationReplicaTest_measurable r hW hF k) hi hWD
        (restorationReplicaTest_bound r hD hB hWD hFB k), hk]
    ring

lemma restoration_ratio_tendsto {Ω : ℕ→Type*} {Ω' : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    (μ : (n : ℕ)→Measure (Ω n)) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {a b : ℝ} (ha : 0<a)
    (A : (n : ℕ)→Ω n→ℝ) (A' : Ω'→ℝ)
    (Z : (n : ℕ)→Ω n→Icc a b) (Z' : Ω'→Icc a b)
    (hA : ∀ n, Measurable (A n)) (hA' : Measurable A')
    (hZ : ∀ n, Measurable (Z n)) (hZ' : Measurable Z')
    {C : ℝ} (hC : 0≤C) (hb : ∀ n x, |A n x|≤C) (hb' : ∀ x, |A' x|≤C)
    (hm : ∀ k : ℕ, Tendsto (fun n => ∫ x, A n x*(Z n x).val^k ∂μ n) atTop
      (𝓝 (∫ x, A' x*(Z' x).val^k ∂ν))) (r : ℕ) :
    Tendsto (fun n => ∫ x, A n x/(Z n x).val^r ∂μ n) atTop
      (𝓝 (∫ x, A' x/(Z' x).val^r ∂ν)) := by
  let F : C(Icc a b,ℝ) := ⟨fun z => (z.val^r)⁻¹,
    (continuous_subtype_val.pow r).inv₀ fun x => pow_ne_zero _ (ne_of_gt (ha.trans_le x.prop.1))⟩
  simpa only [F, ContinuousMap.coe_mk, div_eq_mul_inv] using bounded_weighted_moment_limit μ ν A A' Z Z' hA hA' hZ hZ'
    C hC hb hb' hm F

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

lemma bulkMarkedTest_bound (N r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) (x : Fin r → NormalizedSpin N) :
    |bulkMarkedTest N r F Ψ Φ z x| ≤ ‖F‖*‖Ψ‖*‖Φ‖ := by
  unfold bulkMarkedTest
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (F.norm_coe_le_norm _) (Ψ.norm_coe_le_norm _)
    (abs_nonneg _) (norm_nonneg _)) (Φ.norm_coe_le_norm _) (abs_nonneg _) (by positivity)

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

lemma bulkFreshNumerator_bound (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (p : TwoFreshDisorder (n+1) M) :
    |bulkFreshNumerator n M r f v F Ψ Φ p| ≤
      ‖F‖*‖restorationMarkTest r f Ψ 0‖*‖restorationMarkTest r f Φ 0‖ := by
  apply gibbsReplicaMean_bound_of_integrable (unitSphereLaw (n+1))
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_const.prodMk measurable_id))
    ((bulkMarkedTest_continuous (n+1) r F (restorationMarkTest r f Ψ 0)
      (restorationMarkTest r f Φ 0)).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v p.1)
  exact bulkMarkedTest_bound _ _ _ _ _ _

lemma bulkMarked_replica_moment (N r : ℕ) (μ : Measure (NormalizedSpin N)) [IsProbabilityMeasure μ]
    {H : NormalizedSpin N → ℝ} (hH : Measurable H) (he : Integrable (fun x => Real.exp (H x)) μ)
    (f : ℝ →ᵇ ℝ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (k : ℕ) (z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) :
    (tiltMean μ H (fun x => Real.exp (f (inner ℝ x.val z.1)+f (inner ℝ x.val z.2))) 1)^k *
      gibbsReplicaMean μ H r (bulkMarkedTest N r F (restorationMarkTest r f Ψ 0)
        (restorationMarkTest r f Φ 0) z) =
      gibbsReplicaMean μ H (r+k) (bulkMarkedTest N (r+k) (restorationBlockTest r F k)
        (restorationMarkTest r f Ψ k) (restorationMarkTest r f Φ k) z) := by
  let W := fun x : NormalizedSpin N => Real.exp (f (inner ℝ x.val z.1)+f (inner ℝ x.val z.2))
  let A := bulkMarkedTest N r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) z
  have hW : Measurable W := ((f.measurable.comp (measurable_subtype_coe.inner measurable_const)).add
    (f.measurable.comp (measurable_subtype_coe.inner measurable_const))).exp
  have hpA : Continuous (fun x : Fin r → NormalizedSpin N => (z,x)) :=
    continuous_const.prodMk continuous_id
  have hA : Measurable A := ((bulkMarkedTest_continuous N r F (restorationMarkTest r f Ψ 0)
    (restorationMarkTest r f Φ 0)).comp hpA).measurable
  have hWb (x) : |W x|≤Real.exp (2*‖f‖) := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (le_abs_self (f (inner ℝ x.val z.1))).trans (f.norm_coe_le_norm _)
    have := (le_abs_self (f (inner ℝ x.val z.2))).trans (f.norm_coe_le_norm _)
    linarith
  have h := restoration_replica_moment μ hH hW hA he (Real.exp_pos _).le (by positivity)
    hWb (bulkMarkedTest_bound N r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) z) k
  change _ = _ at h
  rw [←h]
  congr 1
  funext x
  have h₀ := funext (restorationReplicaTest_twoMarks f F Ψ Φ z.1 z.2 0)
  change _ = A at h₀
  rw [←h₀]
  exact restorationReplicaTest_twoMarks f F Ψ Φ z.1 z.2 k x

lemma bulkFresh_polynomial_moment (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (k : ℕ) (p : TwoFreshDisorder (n+1) M) :
    bulkFreshDenominator n M f v p^k*bulkFreshNumerator n M r f v F Ψ Φ p =
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
        (r+k) (bulkMarkedTest (n+1) (r+k) (restorationBlockTest r F k)
          (restorationMarkTest r f Ψ k) (restorationMarkTest r f Φ k) p.2) := by
  exact bulkMarked_replica_moment (n+1) r (unitSphereLaw (n+1))
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v p.1) f F Ψ Φ k p.2

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

lemma bulkFreshCompactDenominator_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) :
    Measurable (bulkFreshCompactDenominator n M f v) :=
  (bulkFreshDenominator_measurable n M f v).subtype_mk

lemma bulkFresh_weighted_integrable (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (k : ℕ) :
    Integrable (fun p => bulkFreshNumerator n M r f v F Ψ Φ p * bulkFreshDenominator n M f v p^k)
      (twoFreshDisorderLaw (n+1) M) := by
  let T : C(Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)),ℝ) :=
    ⟨fun z => z.val^k,continuous_subtype_val.pow k⟩
  exact weighted_compact_integrable (twoFreshDisorderLaw (n+1) M)
    (bulkFreshNumerator n M r f v F Ψ Φ) (bulkFreshNumerator_measurable n M r f v F Ψ Φ)
    (bulkFreshCompactDenominator n M f v) (bulkFreshCompactDenominator_measurable n M f v)
    _ (by positivity) (bulkFreshNumerator_bound n M r f v F Ψ Φ) T

lemma bulkFresh_annealed_polynomial (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (k : ℕ) :
    (∫ p, bulkFreshNumerator n M r f v F Ψ Φ p * bulkFreshDenominator n M f v p^k
      ∂twoFreshDisorderLaw (n+1) M) =
      ∫ Q, (restorationBlockTest r F k * freshMarkedCompactBlockKernel (restorationMarkTest r f Ψ k) *
        freshMarkedCompactBlockKernel (restorationMarkTest r f Φ k)) (compactBlock (r+k) Q)
        ∂bulkGibbsArrayLaw n M f v := by
  rw [twoFreshDisorderLaw,integral_prod _ (bulkFresh_weighted_integrable n M r f v F Ψ Φ k)]
  simp_rw [mul_comm (bulkFreshNumerator n M r f v F Ψ Φ _),bulkFresh_polynomial_moment]
  exact bulk_twoFresh_block n M (r+k) f v (restorationBlockTest r F k)
    (restorationMarkTest r f Ψ k) (restorationMarkTest r f Φ k)

lemma bulkFresh_moment_tendsto (M : ℕ → ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℕ → ℝ) (s : ℕ → ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hν : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν))
    (r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (k : ℕ) :
    Tendsto (fun n => ∫ p, bulkFreshNumerator (s n) (M (s n)) r f (v (s n)) F Ψ Φ p *
      bulkFreshDenominator (s n) (M (s n)) f (v (s n)) p^k ∂twoFreshDisorderLaw (s n+1) (M (s n)))
      atTop (𝓝 (∫ Q, (restorationBlockTest r F k * freshMarkedCompactBlockKernel (restorationMarkTest r f Ψ k) *
        freshMarkedCompactBlockKernel (restorationMarkTest r f Φ k)) (compactBlock (r+k) Q) ∂ν)) := by
  simp_rw [bulkFresh_annealed_polynomial]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    ((restorationBlockTest r F k * freshMarkedCompactBlockKernel (restorationMarkTest r f Ψ k) *
      freshMarkedCompactBlockKernel (restorationMarkTest r f Φ k)).compContinuous
        ⟨compactBlock (r+k), compactBlock_continuous (r+k)⟩)).continuousAt.tendsto.comp hν

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGEvents
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

lemma compactGG_events (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (hn : 0<n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock CompactJointOverlap n →ᵇ ℝ) (g : CompactJointOverlap →ᵇ ℝ),
      compactGGDefect μ n i f g=0)
    (s : Set (CompactBlock CompactJointOverlap n)) (hs : MeasurableSet s)
    (t : Set CompactJointOverlap) (ht : MeasurableSet t) :
    (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t}/n+
      (∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}))/n := by
  classical
  have he := congrArg (fun ρ : Measure (CompactBlock CompactJointOverlap n × CompactJointOverlap) =>
    ρ.real (s×ˢt)) (compactGG_joint_law μ hn i hGG)
  have hb := (compactBlock_continuous (K:=CompactJointOverlap) n).measurable
  have hm (i j : ℕ) : Measurable (fun Q : CompactArray CompactJointOverlap => Q i j) := by fun_prop
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
      ((μ : Measure _).map (fun Q : CompactArray CompactJointOverlap => Q 0 1))).real (s×ˢt) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t} := by
    simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      Measure.map_apply hb hs,Measure.map_apply (hm 0 1) ht]
    rfl
  rw [hprod] at he
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at he
  change (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) = (n:ℝ)⁻¹*(_+_) at he
  rw [he]
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGFiniteCode
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

section

variable {L : Type*} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

lemma compactCodeArray_measurable {L : Type*} [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] {χ : CompactJointOverlap → L} (hχ : Measurable χ) :
    Measurable (compactCodeArray χ) := by
  unfold compactCodeArray
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma compactCodeBlock_measurable {L : Type*} [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] {χ : CompactJointOverlap → L} (hχ : Measurable χ) (n : ℕ) :
    Measurable (compactCodeBlock (n:=n) χ) := by
  unfold compactCodeBlock
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma compactGG_finite_pushforward (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    {χ : CompactJointOverlap → L} (hχ : Measurable χ) :
    FiniteGG ((μ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)) := by
  classical
  intro n hn i A c
  have hm := compactCodeArray_measurable hχ
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
  exact compactGG_events μ n (by omega) i (hGG n i)
    ((compactCodeBlock χ) ⁻¹' {A}) ((measurableSet_singleton A).preimage (compactCodeBlock_measurable hχ n))
    (χ ⁻¹' {c}) ((measurableSet_singleton c).preimage hχ)

lemma compact_finite_code_block_unique [LinearOrder L]
    (μ ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGGμ : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    (hGGν : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν n i f g=0)
    {χ : CompactJointOverlap → L} (hχ : Measurable χ) (d : L)
    (hμ : ∀ᵐ Q ∂(μ : Measure (CompactArray CompactJointOverlap)), (∀ i j, χ (Q i j)=χ (Q j i)) ∧
      (∀ i, χ (Q i i)=d) ∧ ∀ i j k, min (χ (Q i j)) (χ (Q i k)) ≤ χ (Q j k))
    (hν : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), (∀ i j, χ (Q i j)=χ (Q j i)) ∧
      (∀ i, χ (Q i i)=d) ∧ ∀ i j k, min (χ (Q i j)) (χ (Q i k)) ≤ χ (Q j k))
    (hpair : (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => χ (Q 0 1))=
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => χ (Q 0 1))) (n : ℕ) :
    (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => compactCodeBlock (n:=n+1) χ (compactBlock (n+1) Q))=
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => compactCodeBlock (n:=n+1) χ (compactBlock (n+1) Q)) := by
  let μ' := (μ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)
  let ν' := (ν : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)
  have hm := compactCodeArray_measurable hχ
  have : IsProbabilityMeasure μ' := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure ν' := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hgρ (ρ : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (hρ : ∀ᵐ Q ∂(ρ : Measure (CompactArray CompactJointOverlap)), (∀ i j, χ (Q i j)=χ (Q j i)) ∧
        (∀ i, χ (Q i i)=d) ∧ ∀ i j k, min (χ (Q i j)) (χ (Q i k)) ≤ χ (Q j k)) :
      ∀ᵐ R ∂(ρ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ), (∀ i j, R i j=R j i) ∧
        (∀ i, R i i=d) ∧ ∀ i j k, min (R i j) (R i k) ≤ R j k := by
    apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    exact hρ
  have hp : ∀ c, μ'.real {R | R 0 1=c}=ν'.real {R | R 0 1=c} := by
    intro c
    have hh := congrArg (fun ρ : Measure L => ρ.real {c}) hpair
    have he : Measurable (fun Q : CompactArray CompactJointOverlap => χ (Q 0 1)) := hχ.comp (by fun_prop)
    rw [map_measureReal_apply he (measurableSet_singleton c),
      map_measureReal_apply he (measurableSet_singleton c)] at hh
    change ((μ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)).real {R | R 0 1=c} =
      ((ν : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)).real {R | R 0 1=c}
    rw [map_measureReal_apply hm (by measurability : MeasurableSet {R : FiniteOverlap L | R 0 1=c}),
      map_measureReal_apply hm (by measurability : MeasurableSet {R : FiniteOverlap L | R 0 1=c})]
    change (μ : Measure (CompactArray CompactJointOverlap)).real {Q | χ (Q 0 1)=c} =
      (ν : Measure (CompactArray CompactJointOverlap)).real {Q | χ (Q 0 1)=c}
    exact hh

  have he := finiteGG_block_law_unique μ' ν' d (hgρ μ hμ) (hgρ ν hν)
    (compactGG_finite_pushforward μ hGGμ hχ) (compactGG_finite_pushforward ν hGGν hχ) hp n
  dsimp only [μ',ν'] at he
  rw [Measure.map_map (finiteBlock_measurable (n+1)) hm,
    Measure.map_map (finiteBlock_measurable (n+1)) hm] at he
  have hf : finiteBlock (L:=L) (n+1) ∘ compactCodeArray χ =
      fun Q => compactCodeBlock (n:=n+1) χ (compactBlock (n+1) Q) := by
    funext Q i j
    rfl
  rw [hf] at he
  exact he

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformQuantileCells
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma uniformQuantileGrid_last (n : ℕ) : uniformQuantileGrid n (Fin.last (n+1))=1 := by
  apply Subtype.ext
  change ((n+1:ℕ):ℝ)/(n+1)=1
  push_cast
  exact div_self (by positivity)

lemma uniformQuantileCell_mono (n : ℕ) : Monotone (uniformQuantileCell n) := by
  intro u v huv
  change min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n ≤ min ⌊(n+1:ℝ)*(v:ℝ)⌋₊ n
  exact min_le_min_right _ (Nat.floor_mono (mul_le_mul_of_nonneg_left (show (u:ℝ)≤v from huv) (by positivity)))

lemma uniformQuantileCell_measurable (n : ℕ) : Measurable (uniformQuantileCell n) :=
  (uniformQuantileCell_mono n).measurable

lemma uniformQuantileCell_floor {n : ℕ} {u : Time} (hu : (u:ℝ)<1) :
    (uniformQuantileCell n u).val=⌊(n+1:ℝ)*(u:ℝ)⌋₊ := by
  change min _ n=_
  apply min_eq_left
  have hf : ⌊(n+1:ℝ)*(u:ℝ)⌋₊<n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) u.2.1)]
    push_cast
    nlinarith
  omega

lemma uniformQuantileCell_bounds (n : ℕ) (u : Time) :
    uniformQuantileGrid n (uniformQuantileCell n u).castSucc≤u ∧
      u≤uniformQuantileGrid n (uniformQuantileCell n u).succ := by
  by_cases hu : (u:ℝ)<1
  · have he := uniformQuantileCell_floor (n:=n) hu
    constructor
    · change ((uniformQuantileCell n u).val:ℝ)/(n+1)≤u
      rw [he,div_le_iff₀ (by positivity)]
      simpa only [mul_comm] using Nat.floor_le (mul_nonneg (show (0:ℝ)≤(n:ℝ)+1 by positivity) u.2.1)
    · change (u:ℝ)≤((_ : ℕ):ℝ)/(n+1)
      rw [Fin.val_succ,he,le_div_iff₀ (by positivity)]
      push_cast
      simpa only [mul_comm] using (Nat.lt_floor_add_one ((n+1:ℝ)*(u:ℝ))).le
  · have he : u=1 := Subtype.ext (le_antisymm u.2.2 (le_of_not_gt hu))
    subst u
    have hcell : uniformQuantileCell n 1=Fin.last n := by
      apply Fin.ext
      change min ⌊(n+1:ℝ)*1⌋₊ n=n
      rw [mul_one,show (n:ℝ)+1=((n+1:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast]
      omega
    rw [hcell,Fin.succ_last,uniformQuantileGrid_last]
    exact ⟨le_top,le_rfl⟩

lemma compactSpinTime_continuous : Continuous compactSpinTime := by
  unfold compactSpinTime
  fun_prop

lemma compactSpinTime_mono : Monotone compactSpinTime := by
  intro x y hxy
  change (x.val+1)/2 ≤ (y.val+1)/2
  have : x.val ≤ y.val := hxy
  linarith

lemma compactSpinCode_measurable (n : ℕ) : Measurable (compactSpinCode n) :=
  (uniformQuantileCell_measurable n).comp (compactSpinTime_continuous.measurable.comp measurable_fst)

lemma compactSpinCode_mono (n : ℕ) {x y : CompactJointOverlap} (h : x.1.val ≤ y.1.val) :
    compactSpinCode n x ≤ compactSpinCode n y :=
  uniformQuantileCell_mono n (compactSpinTime_mono h)

lemma compactSpinDecode_error (n : ℕ) (x : CompactJointOverlap) :
    |compactSpinDecode n (compactSpinCode n x)-x.1.val| ≤ 2/(n+1:ℝ) := by
  obtain ⟨hlo,hhi⟩ := uniformQuantileCell_bounds n (compactSpinTime x.1)
  have hlo' : (uniformQuantileGrid n (compactSpinCode n x).castSucc:ℝ) ≤ (x.1.val+1)/2 := hlo
  have hhi' : (x.1.val+1)/2 ≤ (uniformQuantileGrid n (compactSpinCode n x).succ:ℝ) := hhi
  have hgap : (uniformQuantileGrid n (compactSpinCode n x).succ:ℝ)-
      (uniformQuantileGrid n (compactSpinCode n x).castSucc:ℝ)=1/(n+1:ℝ) := by
    simp only [uniformQuantileGrid,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring
  dsimp only [compactSpinDecode]
  rw [abs_of_nonpos (by linarith)]
  simp only [div_eq_mul_inv,one_mul] at hgap ⊢
  linarith

lemma compactSpinDecode_tendsto (x : CompactJointOverlap) :
    Tendsto (fun n => compactSpinDecode n (compactSpinCode n x)) atTop (𝓝 x.1.val) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n : ℕ => x.1.val-2*(1/(n+1:ℝ))) (h := fun n : ℕ => x.1.val+2*(1/(n+1:ℝ)))
  · simpa using tendsto_const_nhds.sub ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2)
  · simpa using tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2)
  · intro n
    have h := (abs_le.mp (compactSpinDecode_error n x)).1
    simp only [div_eq_mul_inv,one_mul] at h ⊢
    linarith
  · intro n
    have h := (abs_le.mp (compactSpinDecode_error n x)).2
    simp only [div_eq_mul_inv,one_mul] at h ⊢
    linarith

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshGGUniqueness
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compactSpinCode_geometry (n : ℕ) {Q : CompactArray CompactJointOverlap}
    (hQ : CompactSpinGeometry Q) :
    (∀ i j, compactSpinCode n (Q i j)=compactSpinCode n (Q j i)) ∧
      (∀ i, compactSpinCode n (Q i i)=compactSpinCode n (compactSpinTop,0)) ∧
      ∀ i j k, min (compactSpinCode n (Q i j)) (compactSpinCode n (Q i k)) ≤ compactSpinCode n (Q j k) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    exact le_antisymm (compactSpinCode_mono n (hQ.1 i j).le) (compactSpinCode_mono n (hQ.1 i j).ge)
  · intro i
    exact le_antisymm (compactSpinCode_mono n (hQ.2.1 i).le) (compactSpinCode_mono n (hQ.2.1 i).ge)
  · intro i j k
    rcases le_total (Q i j).1.val (Q i k).1.val with h|h
    · apply (min_le_left _ _).trans
      apply compactSpinCode_mono n
      simpa only [min_eq_left h] using hQ.2.2 i j k
    · apply (min_le_right _ _).trans
      apply compactSpinCode_mono n
      simpa only [min_eq_right h] using hQ.2.2 i j k

variable (μ ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
variable (hGGμ : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
variable (hGGν : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν n i f g=0)
variable (hμ : ∀ᵐ Q ∂(μ : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hν : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hpair : (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
  (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))

include hGGμ hGGν hμ hν hpair in
lemma compactSpinCode_block_law_unique (n r : ℕ) :
    (μ : Measure (CompactArray CompactJointOverlap)).map
      (fun Q => compactCodeBlock (n:=r+1) (compactSpinCode n) (compactBlock (r+1) Q))=
    (ν : Measure (CompactArray CompactJointOverlap)).map
      (fun Q => compactCodeBlock (n:=r+1) (compactSpinCode n) (compactBlock (r+1) Q)) := by
  apply compact_finite_code_block_unique μ ν hGGμ hGGν (compactSpinCode_measurable n)
    (compactSpinCode n (compactSpinTop,0))
    (hμ.mono fun Q hQ => compactSpinCode_geometry n hQ)
    (hν.mono fun Q hQ => compactSpinCode_geometry n hQ) _ r
  have he := congrArg (fun ρ : Measure CompactOverlap =>
    ρ.map (fun x => uniformQuantileCell n (compactSpinTime x))) hpair
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1) := by fun_prop
  have hc : Measurable (fun x => uniformQuantileCell n (compactSpinTime x)) :=
    (uniformQuantileCell_measurable n).comp compactSpinTime_continuous.measurable
  rw [Measure.map_map hc hm,Measure.map_map hc hm] at he
  exact he

include hGGμ hGGν hμ hν hpair in
lemma compactSpinCode_integral_unique (n r : ℕ) (F : Matrix (Fin (r+1)) (Fin (r+1)) ℝ →ᵇ ℝ) :
    (∫ Q, F (fun i j => compactSpinDecode n (compactSpinCode n (Q i j))) ∂(μ : Measure (CompactArray CompactJointOverlap)))=
    ∫ Q, F (fun i j => compactSpinDecode n (compactSpinCode n (Q i j))) ∂(ν : Measure (CompactArray CompactJointOverlap)) := by
  let D : FiniteBlock (Fin (n+1)) (r+1) → ℝ := fun A => F (fun i j => compactSpinDecode n (A i j))
  have hD : Measurable D := measurable_of_countable _
  have hm : Measurable (fun Q : CompactArray CompactJointOverlap =>
      compactCodeBlock (n:=r+1) (compactSpinCode n) (compactBlock (r+1) Q)) :=
    (compactCodeBlock_measurable (compactSpinCode_measurable n) (r+1)).comp (compactBlock_continuous (r+1)).measurable
  have he := congrArg (fun ρ : Measure (FiniteBlock (Fin (n+1)) (r+1)) => ∫ A, D A ∂ρ)
    (compactSpinCode_block_law_unique μ ν hGGμ hGGν hμ hν hpair n r)
  rw [integral_map hm.aemeasurable hD.aestronglyMeasurable,
    integral_map hm.aemeasurable hD.aestronglyMeasurable] at he
  exact he

lemma compactSpinCode_integral_tendsto (ρ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ Q, F (fun i j => compactSpinDecode n (compactSpinCode n (Q i j)))
      ∂(ρ : Measure (CompactArray CompactJointOverlap))) atTop
      (𝓝 (∫ Q, F (fun i j => (Q i j).1.val) ∂(ρ : Measure (CompactArray CompactJointOverlap)))) := by
  let : MeasurableSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (MeasurableSpace (Fin r → Fin r → ℝ))
  let : BorelSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (BorelSpace (Fin r → Fin r → ℝ))
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    apply (F.continuous.measurable.comp _).aestronglyMeasurable
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_of_countable (compactSpinDecode n)).comp ((compactSpinCode_measurable n).comp (by fun_prop))
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun Q => F.norm_coe_le_norm _
  · exact ae_of_all _ fun Q => F.continuous.continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => compactSpinDecode_tendsto (Q i j))

include hGGμ hGGν hμ hν hpair in

theorem scalarGram_eq_of_pair_law (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    (∫ Q, F (fun i j => (Q i j).1.val) ∂(μ : Measure (CompactArray CompactJointOverlap)))=
    ∫ Q, F (fun i j => (Q i j).1.val) ∂(ν : Measure (CompactArray CompactJointOverlap)) := by
  cases r with
  | zero =>
    have he : ∀ Q : CompactArray CompactJointOverlap,
        F (fun i j : Fin 0 => (Q i j).1.val)=F (fun _ _ => 0) := by
      intro Q
      congr 1
      exact Subsingleton.elim _ _
    simp only [he,integral_const,probReal_univ,one_smul]
  | succ r =>
    have h1 := compactSpinCode_integral_tendsto μ (r+1) F
    have h2 := compactSpinCode_integral_tendsto ν (r+1) F
    have he := compactSpinCode_integral_unique μ ν hGGμ hGGν hμ hν hpair
    simp_rw [he] at h1
    exact tendsto_nhds_unique h1 h2

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma quantileSpinLaw_integral (q : Time→Time) (hq : Measurable q)
    (F : CompactOverlap→ℝ) (hF : Measurable F) :
    (∫ x, F x ∂(quantileSpinLaw q hq : Measure CompactOverlap))=∫ u, F (timeSpin (q u)) ∂timeLaw :=
  integral_map (timeSpin_continuous.measurable.comp hq).aemeasurable hF.aestronglyMeasurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_FreshControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compactPositivePairLaw_spin_quantile
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hn : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val) :
    (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
      (quantileSpinLaw (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))
        (boundedQuantile_measurable _) : Measure CompactOverlap) := by
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  change _=timeLaw.map (timeSpin ∘ boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))
  rw [←Measure.map_map timeSpin_continuous.measurable (boundedQuantile_measurable _),
    timeLaw_eq_volume,boundedQuantile_law]
  unfold compactPositivePairLaw
  rw [Measure.map_map (f := fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1))
    measurable_fst (by exact compactPositivePair_measurable.comp (by fun_prop))]
  rw [Measure.map_map timeSpin_continuous.measurable
    (show Measurable (Prod.fst ∘ fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) from
      measurable_fst.comp (compactPositivePair_measurable.comp (by fun_prop)))]
  apply Measure.map_congr
  filter_upwards [hn] with Q hQ
  apply Subtype.ext
  change (Q 0 1).1.val=max 0 (Q 0 1).1.val
  exact (max_eq_right hQ).symm

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelPairTestValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma restorationMarkTest_gaussianMixed {r : ℕ} (f : ℝ →ᵇ ℝ) (v : Fin r → ℝ →ᵇ ℝ) (j : ℕ) :
    restorationMarkTest r f (gaussianMixedTest v) j =
      gaussianMixedTest (labelRestoredFunctions f v j) := by
  induction j with
  | zero =>
    ext x
    simp only [restorationMarkTest,BoundedContinuousFunction.mul_apply,gaussianReplicaTest_apply,
      gaussianMixedTest_apply,labelRestoredFunctions,Finset.prod_mul_distrib]
    rfl
  | succ j hj =>
    ext x
    change (expBCF 1 f) (x 0) * restorationMarkTest r f (gaussianMixedTest v) j
      (WithLp.toLp 2 (fun i => x i.succ)) =
        gaussianMixedTest (Fin.cons (expBCF 1 f) (labelRestoredFunctions f v j)) x
    rw [hj]
    simp only [gaussianMixedTest_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma scalarFrontMatrixTest_compact (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactOverlap (r+j)) :
    scalarFrontMatrixTest r F j (fun i l => (Q i l).val) =
      restorationBlockTest r (F.compContinuous ⟨fun Q i l => (Q i l).val,by fun_prop⟩) j Q := by
  induction j with
  | zero => rfl
  | succ j hj => exact hj _

lemma scalarRestorationPairMoment_compact (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactOverlap (2+j)) :
    scalarRestorationPairMoment f v w F j (fun i l => (Q i l).val) =
      (restorationBlockTest 2 (compactPairTest F) j *
        freshMarkedCompactBlockKernel (restorationMarkTest 2 f (gaussianMixedTest (fun _ => v)) j) *
        freshMarkedCompactBlockKernel (restorationMarkTest 2 f (gaussianMixedTest (fun _ => w)) j)) Q := by
  have he : (scalarPairMatrixTest F).compContinuous
      ⟨fun Q : CompactBlock CompactOverlap 2 => fun i l => (Q i l).val,by fun_prop⟩=compactPairTest F := by
    ext Q
    change F (Set.projIcc (-1) 1 (by norm_num : (-1:ℝ)≤1) (Q 1 0).val)=F (Q 1 0)
    rw [Set.projIcc_of_mem _ (Q 1 0).prop]
  change scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j (fun i l => (Q i l).val) *
      freshMarkedMatrixKernel _ (fun i l => (Q i l).val) * freshMarkedMatrixKernel _ (fun i l => (Q i l).val) = _
  rw [scalarFrontMatrixTest_compact,he]
  simp only [BoundedContinuousFunction.mul_apply,restorationMarkTest_gaussianMixed]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactRestorationWitness
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

lemma pairRestorationBound_nonneg (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) :
    0≤pairRestorationBound f v w F := by unfold pairRestorationBound; positivity

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkLimitGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

lemma bulkJointLaw_scalarGram_integral (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    (∫ Q : CompactArray CompactJointOverlap, F (fun i j => (Q i j).1.val) ∂(bulkJointLaw ν : Measure _))=
      ∫ Q : CompactArray CompactOverlap, F (fun i j => (Q i j).val) ∂(ν : Measure _) := by
  exact compactMapLaw_integral bulkJointEmbedding bulkJointEmbedding_continuous ν
    (fun Q => F (fun i j => (Q i j).1.val)) (F.continuous.comp (by fun_prop)).measurable

lemma bulk_pair_restoration_ratio_tendsto (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (F : CompactOverlap →ᵇ ℝ) :
    Tendsto (fun n => ∫ p, bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
      (compactPairTest F) (gaussianMixedTest (fun _ => 1)) (gaussianMixedTest (fun _ => 1)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ Q : CompactArray CompactOverlap, F (Q 0 1) ∂(ν : Measure _))) := by
  let q := boundedQuantile ((compactPositivePairLaw (bulkJointLaw ν)).map Prod.fst)
  obtain ⟨ρ,η,hG,hge,hp,hm,hl⟩ := quantile_pair_reference_exists q (boundedQuantile_monotone _) g F
  have hpair := (compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn).trans hp.symm
  have he (j : ℕ) : (∫ x, x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
      ∫ Q : CompactArray CompactOverlap, scalarRestorationPairMoment g.f 1 1 F j
        (fun i l => (Q i l).val) ∂(ν : Measure _) := by
    rw [hm j,←scalarGram_eq_of_pair_law (bulkJointLaw ν) ρ hGG hG hgeo hge hpair]
    exact bulkJointLaw_scalarGram_integral ν _ _
  let Ψ : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ := gaussianMixedTest (fun _ => (1 : ℝ →ᵇ ℝ))
  let C := ‖compactPairTest F‖*‖restorationMarkTest 2 g.f Ψ 0‖*‖restorationMarkTest 2 g.f Ψ 0‖+
    pairRestorationBound g.f 1 1 F
  have hC : 0≤C := add_nonneg (by positivity) (pairRestorationBound_nonneg _ _ _ _)
  have hηB (x : WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)) : |x.1.val|≤C :=
    (abs_le.mpr x.1.prop).trans (le_add_of_nonneg_left (by positivity))
  have hb (n : ℕ) (p : TwoFreshDisorder (s n+1) (M (s n))) :
      |bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Ψ p|≤C :=
    (bulkFreshNumerator_bound _ _ _ _ _ _ _ _ _).trans
      (le_add_of_nonneg_right (pairRestorationBound_nonneg _ _ _ _))
  have hmoment j : Tendsto (fun n => ∫ p,
      bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Ψ p *
      (bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n)) p).val^j
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))) := by
    rw [he j]
    simp_rw [scalarRestorationPairMoment_compact]
    exact bulkFresh_moment_tendsto M g.f v s hlim 2 (compactPairTest F) Ψ Ψ j
  have ht := restoration_ratio_tendsto
    (fun n => twoFreshDisorderLaw (s n+1) (M (s n)))
    (η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)))
    (Real.exp_pos _)
    (fun n => bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Ψ)
    (fun x => x.1.val)
    (fun n => bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n))) (fun x => x.2)
    (fun n => bulkFreshNumerator_measurable _ _ _ _ _ _ _ _) (by fun_prop)
    (fun n => bulkFreshCompactDenominator_measurable _ _ _ _) (by fun_prop)
    hC hb hηB hmoment 2
  have hvalue : (∫ x,x.1.val/x.2.val^2
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _) := by
    simp only [div_eq_mul_inv]
    change (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=_
    rw [hl,←compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn]
    have hi := integral_map (μ := (bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)))
      (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable
      (show Measurable (fun z : CompactOverlap => F z) from F.continuous.measurable).aestronglyMeasurable
    refine hi.trans ?_
    exact compactMapLaw_integral bulkJointEmbedding bulkJointEmbedding_continuous ν
      (fun Q => F (Q 0 1).1) (by fun_prop)
  rw [hvalue] at ht
  exact ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedPairLimit
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

lemma bulk_marked_ratio_tendsto_of_reference (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (w w' : ℝ→ᵇℝ) (F : CompactOverlap→ᵇℝ)
    (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F)))
    (hm : ∀ j,(∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationPairMoment g.f w w' F j
        (fun i l => (Q i l).val) ∂(ν : Measure _)) :
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
      (compactPairTest F) (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 2 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F))))) := by
  let Ψ : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ := gaussianMixedTest (fun _ => w)
  let Φ : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ := gaussianMixedTest (fun _ => w')
  let C := ‖compactPairTest F‖*‖restorationMarkTest 2 g.f Ψ 0‖*‖restorationMarkTest 2 g.f Φ 0‖+
    pairRestorationBound g.f w w' F
  have hC : 0≤C := add_nonneg (by positivity) (pairRestorationBound_nonneg _ _ _ _)
  have hηB (x : WeightedRestorationRange g.f (pairRestorationBound g.f w w' F)) : |x.1.val|≤C :=
    (abs_le.mpr x.1.prop).trans (le_add_of_nonneg_left (by positivity))
  have hb (n : ℕ) (p : TwoFreshDisorder (s n+1) (M (s n))) :
      |bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Φ p|≤C :=
    (bulkFreshNumerator_bound _ _ _ _ _ _ _ _ _).trans
      (le_add_of_nonneg_right (pairRestorationBound_nonneg _ _ _ _))
  have hmoment j : Tendsto (fun n => ∫ p,
      bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Φ p *
      (bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n)) p).val^j
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F))))) := by
    rw [hm j]
    simp_rw [scalarRestorationPairMoment_compact]
    exact bulkFresh_moment_tendsto M g.f v s hlim 2 (compactPairTest F) Ψ Φ j
  have ht := restoration_ratio_tendsto
    (fun n => twoFreshDisorderLaw (s n+1) (M (s n)))
    (η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F)))
    (Real.exp_pos _)
    (fun n => bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Φ)
    (fun x => x.1.val)
    (fun n => bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n))) (fun x => x.2)
    (fun n => bulkFreshNumerator_measurable _ _ _ _ _ _ _ _) (by fun_prop)
    (fun n => bulkFreshCompactDenominator_measurable _ _ _ _) (by fun_prop)
    hC hb hηB hmoment 2
  simpa only [div_eq_mul_inv, restorationReciprocal, ContinuousMap.coe_mk, bulkFreshCompactDenominator, Ψ, Φ] using ht

theorem bulk_marked_pair_limit_exists (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤‖w‖^2) ∧
      ∀ (F : CompactOverlap→ᵇℝ) (b : Bool),
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
      (compactPairTest F) (gaussianMixedTest (fun _=>w))
      (gaussianMixedTest (fun _=>secondPairMark w b)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^(pairMarkPower b) ∂(ν : Measure _))) := by
  let q := boundedQuantile ((compactPositivePairLaw (bulkJointLaw ν)).map Prod.fst)
  have hq : Monotone q := boundedQuantile_monotone _
  obtain ⟨a,ham,hab,href⟩ := quantile_marked_pair_reference_exists q hq g w
  refine ⟨a,ham,hab,fun F b => ?_⟩
  obtain ⟨ρ,η,hG,hge,hp,hm,hl⟩ := href F b
  have hpair := (compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn).trans hp.symm
  have he (j : ℕ) : (∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w (secondPairMark w b) F))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationPairMoment g.f w (secondPairMark w b) F j
        (fun i l => (Q i l).val) ∂(ν : Measure _) := by
    rw [hm j,←scalarGram_eq_of_pair_law (bulkJointLaw ν) ρ hGG hG hgeo hge hpair]
    exact bulkJointLaw_scalarGram_integral ν _ _
  have ht := bulk_marked_ratio_tendsto_of_reference M g v s hlim w (secondPairMark w b) F η he
  rw [hl] at ht
  have hmG : Measurable (fun z : CompactOverlap => F z*(a z.val)^(pairMarkPower b)) :=
    F.measurable.mul ((ham.measurable.comp measurable_subtype_coe).pow_const _)
  have hvalue : (∫ u,F (timeSpin (q u))*(a (q u))^(pairMarkPower b) ∂timeLaw)=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^(pairMarkPower b) ∂(ν : Measure _) := by
    change (∫ u,F (timeSpin (q u))*(a (timeSpin (q u)).val)^(pairMarkPower b) ∂timeLaw)=_
    rw [←quantileSpinLaw_integral q hq.measurable (fun z => F z*(a z.val)^(pairMarkPower b)) hmG,
      ←compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn]
    have hi := integral_map (μ := (bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)))
      (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable hmG.aestronglyMeasurable
    refine hi.trans ?_
    exact compactMapLaw_integral bulkJointEmbedding bulkJointEmbedding_continuous ν
      (fun Q => F (Q 0 1).1*(a (Q 0 1).1.val)^(pairMarkPower b))
      (F.measurable.comp (by fun_prop) |>.mul ((ham.measurable.comp (by fun_prop)).pow_const _))
  rwa [hvalue] at ht

lemma bulkPairOverlapTest_measurable (n : ℕ) (F : CompactOverlap→ᵇℝ) : Measurable (bulkPairOverlapTest n F) := by
  unfold bulkPairOverlapTest bulkOverlap spinOverlap
  fun_prop

lemma bulk_marked_last_pair (n M : ℕ) (f w w' : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : CompactOverlap→ᵇℝ) :
    bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*
      pairFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x)*
      pairFieldMark w' (bulkPatternFields (Fin.last (M+1)) a x))=
    ∫ p,bulkFreshNumerator n M 2 f v (compactPairTest F)
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator n M f v p^2 ∂twoFreshDisorderLaw (n+1) M := by
  rw [←bulkFresh_annealed_restoration]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    congr 1

lemma bulkPairAverage_first (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (F : CompactOverlap→ᵇℝ) :
    bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*bulkPairAverage n (M+2) w a x)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)*(∫ p,bulkFreshNumerator n M 2 f v (compactPairTest F)
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
      bulkFreshDenominator n M f v p^2 ∂twoFreshDisorderLaw (n+1) M) := by
  have hf : (fun a x => bulkPairOverlapTest n F x*bulkPairAverage n (M+2) w a x)=
      (fun a x => ((n+1:ℕ):ℝ)⁻¹*(bulkPairOverlapTest n F x*∑ i,pairFieldMark w (bulkPatternFields i a x))) := by
    funext a x; unfold bulkPairAverage; ring
  rw [hf,bulkReplicaMean_const_mul,bulk_pattern_sum_first n (M+2) 2 f v _ (bulkPairOverlapTest_measurable n F)
    _ (pairFieldMark_measurable w) (norm_nonneg F) (sq_nonneg ‖w‖)
    (fun x => F.norm_coe_le_norm _) (pairFieldMark_bound w) ((Fin.last M).castSucc)]
  rw [←bulk_marked_last_pair n M f w 1 v F]
  simp only [pairFieldMark,BoundedContinuousFunction.coe_one,Pi.one_apply,Finset.prod_const_one,mul_one]
  ring

lemma bulkPairAverage_second (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (F : CompactOverlap→ᵇℝ) :
    bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*(bulkPairAverage n (M+2) w a x)^2)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)^2*
      bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*
        (pairFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)+
    (((M+2:ℕ):ℝ)*((M+1:ℕ):ℝ)/(n+1:ℕ)^2)*(∫ p,bulkFreshNumerator n M 2 f v (compactPairTest F)
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
      bulkFreshDenominator n M f v p^2 ∂twoFreshDisorderLaw (n+1) M) := by
  have hf : (fun a x => bulkPairOverlapTest n F x*(bulkPairAverage n (M+2) w a x)^2)=
      (fun a x => (((n+1:ℕ):ℝ)⁻¹)^2*(bulkPairOverlapTest n F x*(∑ i,pairFieldMark w (bulkPatternFields i a x))^2)) := by
    funext a x; unfold bulkPairAverage; ring
  have hkl : (Fin.last M).castSucc≠Fin.last (M+1) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at this
    omega
  rw [hf,bulkReplicaMean_const_mul,bulk_pattern_sum_second n (M+2) 2 f v _ (bulkPairOverlapTest_measurable n F)
    _ (pairFieldMark_measurable w) (norm_nonneg F) (sq_nonneg ‖w‖)
    (fun x => F.norm_coe_le_norm _) (pairFieldMark_bound w) ((Fin.last M).castSucc) (Fin.last (M+1)) hkl,
    bulk_marked_last_pair n M f w w v F]
  simp only [div_eq_mul_inv,inv_pow]
  push_cast
  ring

lemma bulkPairAverage_diagonal_bound (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (F : CompactOverlap→ᵇℝ) :
    |bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*
        (pairFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)|≤‖F‖*‖w‖^4 := by
  apply bulkReplicaMean_bound _ _ _ _ _ _
    ((bulkPairOverlapTest_measurable n F |>.comp measurable_snd).mul
      (((pairFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)).pow_const 2)) (by positivity)
  intro a x
  rw [abs_mul,abs_pow]
  apply (mul_le_mul (F.norm_coe_le_norm _) (pow_le_pow_left₀ (abs_nonneg _) (pairFieldMark_bound w _) 2)
    (by positivity) (norm_nonneg _)).trans_eq
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkEmpiricalLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma bulkPairAverage_first_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (α : ℝ) (w : ℝ→ᵇℝ) (a : ℝ→ℝ) (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : ∀ F : CompactOverlap→ᵇℝ,
      Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
        (compactPairTest F) (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
        bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
          ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
        (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1)*a (Q 0 1).val ∂(ν : Measure _))))
    (F : CompactOverlap→ᵇℝ) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*bulkPairAverage (s n) (M (s n)+2) w d x))
      atTop (𝓝 (α*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*a (Q 0 1).val ∂(ν : Measure _)))) := by
  simp_rw [bulkPairAverage_first]
  exact hd.mul (ht F)

lemma bulkPairAverage_second_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ) (w : ℝ→ᵇℝ) (a : ℝ→ℝ)
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : ∀ F : CompactOverlap→ᵇℝ,
      Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
        (compactPairTest F) (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
        bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
          ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
        (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^2 ∂(ν : Measure _))))
    (F : CompactOverlap→ᵇℝ) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*(bulkPairAverage (s n) (M (s n)+2) w d x)^2))
      atTop (𝓝 (α^2*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^2 ∂(ν : Measure _)))) := by
  have hfac := bulk_density_factors M s hs α hd
  have herr : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2*
      bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2 (fun d x => bulkPairOverlapTest (s n) F x*
        (pairFieldMark w (bulkPatternFields ((Fin.last (M (s n))).castSucc) d x))^2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [zero_mul] using hfac.1.mul_const (‖F‖*‖w‖^4))
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2)]
    exact mul_le_mul_of_nonneg_left (bulkPairAverage_diagonal_bound (s n) (M (s n)) g.f w (v (s n)) F) (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2)
  simp_rw [bulkPairAverage_second]
  simpa using herr.add (hfac.2.mul (ht F))

theorem bulk_marked_empirical_limits (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤‖w‖^2) ∧
      ∀ F : CompactOverlap→ᵇℝ,
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*bulkPairAverage (s n) (M (s n)+2) w d x))
      atTop (𝓝 (α*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*a (Q 0 1).val ∂(ν : Measure _)))) ∧
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*(bulkPairAverage (s n) (M (s n)+2) w d x)^2))
      atTop (𝓝 (α^2*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^2 ∂(ν : Measure _)))) := by
  obtain ⟨a,ham,hab,ht⟩ := bulk_marked_pair_limit_exists M g v s hlim hGG hgeo hn w
  refine ⟨a,ham,hab,fun F => ⟨?_,?_⟩⟩
  · apply bulkPairAverage_first_limit M g v s α w a ν hd _ F
    intro F
    simpa [secondPairMark,pairMarkPower] using ht F false
  · apply bulkPairAverage_second_limit M g v s hs α w a ν hd _ F
    intro F
    simpa [secondPairMark,pairMarkPower] using ht F true

lemma bulk_pair_restoration_exact (n M : ℕ) (g : Jet3) (v : ℕ→ℝ)
    (F : CompactOverlap →ᵇ ℝ) :
    (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(bulkGibbsArrayLaw n (M+2) g.f v : Measure _))=
      ∫ p,bulkFreshNumerator n M 2 g.f v (compactPairTest F)
        (gaussianMixedTest (fun _=>1)) (gaussianMixedTest (fun _=>1)) p /
        bulkFreshDenominator n M g.f v p^2 ∂twoFreshDisorderLaw (n+1) M := by
  have he := bulkFresh_annealed_restoration n M 2 g.f v (compactPairTest F)
    (gaussianMixedTest (fun _=>1)) (gaussianMixedTest (fun _=>1))
  let A : CompactBlock CompactOverlap 2 →ᵇ ℝ := F.compContinuous ⟨fun Q=>Q 0 1,by fun_prop⟩
  have hb := bulkGibbsArray_block n (M+2) g.f v 2 A
  change (∫ Q,A (compactBlock 2 Q) ∂(bulkGibbsArrayLaw n (M+2) g.f v : Measure _))=_
  rw [hb,←he]
  apply integral_congr_ae
  filter_upwards [] with a
  congr 1
  funext x
  simp only [bulkMarkedTest,gaussianMixedTest_apply,BoundedContinuousFunction.coe_one,Pi.one_apply,Finset.prod_const_one,mul_one]
  change F (bulkOverlap (x 0) (x 1))=F (bulkOverlap (x 1) (x 0))
  congr 1
  apply Subtype.ext
  exact real_inner_comm _ _

lemma bulk_full_pair_tendsto (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (F : CompactOverlap →ᵇ ℝ) :
    Tendsto (fun n => ∫ Q : CompactArray CompactOverlap,F (Q 0 1)
      ∂(bulkGibbsArrayLaw (s n) (M (s n)+2) g.f (v (s n)) : Measure _)) atTop
      (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _))) := by
  simp_rw [bulk_pair_restoration_exact]
  exact bulk_pair_restoration_ratio_tendsto M g v s hlim hGG hgeo hn F

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactTripleGG
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped BigOperators Topology BoundedContinuousFunction NNReal ContDiff

lemma compact_two_edge_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (F : CompactBlock K 2→ᵇℝ) (g : K→ᵇℝ),compactGGDefect μ 2 0 F g=0) :
    (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 2))=
      (1/2:ℝ≥0) • (((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)))+
      (1/2:ℝ≥0) • ((μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 1))) := by
  have h := compactGG_joint_law μ (n:=2) (by norm_num) 0 hGG
  have hm : Measurable (fun p : CompactBlock K 2×K=>(p.1 0 1,p.2)) := by fun_prop
  have he := congrArg (Measure.map (fun p : CompactBlock K 2×K=>(p.1 0 1,p.2))) h
  simp only [Finset.univ_fin2,Finset.erase_insert,Finset.mem_singleton,Fin.zero_ne_one,not_false_eq_true,
    Finset.sum_singleton] at he
  rw [Measure.map_map hm ((compactBlock_continuous 2).measurable.prodMk (by fun_prop)),Measure.map_smul,Measure.map_add _ _ hm,Measure.map_map hm ((compactBlock_continuous 2).measurable.prodMk (by fun_prop))] at he
  have hp : Measure.map (fun p : CompactBlock K 2×K=>(p.1 0 1,p.2))
      (((μ : Measure (CompactArray K)).map (compactBlock 2)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)))=
      ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)) := by
    change Measure.map (Prod.map (fun A : CompactBlock K 2 => A 0 1) id) _ = _
    rw [←Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
    rw [Measure.map_map (by fun_prop) (compactBlock_continuous 2).measurable]
    rfl
  rw [hp] at he
  simpa [one_div,smul_add,compactBlock,Function.comp_def] using he

lemma ultrametric_tangent_algebra {r s t : ℝ} (h : UltrametricTriangle r s t)
    (a : ℝ→ℝ) :
    a s*t=r*a s-max (r-s) 0*a s+a r*max (t-r) 0 := by
  rcases lt_trichotomy s r with hs|hs|hs
  · have ht : t=s := by
      have h' : UltrametricTriangle s r t := ⟨by simpa [min_comm] using h.1,h.2.2,h.2.1⟩
      exact ultrametric_triangle_small_eq h' hs
    subst t
    rw [max_eq_left (by linarith : 0 ≤ r-s),max_eq_right (by linarith : s-r≤0)]
    ring
  · subst s
    have hr : r≤t := by simpa using h.1
    rw [sub_self,max_self,max_eq_left (by linarith : 0≤t-r)]
    ring
  · have ht := ultrametric_triangle_small_eq h hs
    subst t
    rw [max_eq_right (by linarith : r-s≤0),sub_self,max_self]
    ring

lemma boundedAbs_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (f : Ω→ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x,|f x|≤C) :
    Integrable f P := Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma two_edge_integral {Ω K : Type*} [MeasurableSpace Ω] [MeasurableSpace K]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure K) [IsProbabilityMeasure ν]
    (r s : Ω→K) (hr : Measurable r) (hs : Measurable s)
    (hlaw : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (H : K×K→ℝ) (hH : Measurable H) (C : ℝ) (hb : ∀ x,|H x|≤C) :
    (∫ x,H (r x,s x) ∂P)=(1/2:ℝ)*((∫ x,∫ y,H (x,y) ∂ν ∂ν)+(∫ x,H (x,x) ∂ν)) := by
  have hi : Integrable H (ν.prod ν) := boundedAbs_integrable _ _ hH C hb
  have hd : Integrable H (ν.map fun x=>(x,x)) := boundedAbs_integrable _ _ hH C hb
  rw [←integral_map (hr.prodMk hs).aemeasurable hH.aestronglyMeasurable,hlaw,
    integral_add_measure (hi.smul_measure_nnreal) (hd.smul_measure_nnreal),
    integral_smul_nnreal_measure,integral_smul_nnreal_measure,
    integral_map (show Measurable (fun x : K=>(x,x)) from measurable_id.prodMk measurable_id).aemeasurable hH.aestronglyMeasurable,
    integral_prod _ hi]
  simp only [NNReal.smul_def,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,smul_eq_mul]
  ring

lemma time_abs_le_one (r : Time) : |(r:ℝ)|≤1 := by
  rw [abs_of_nonneg r.property.1]
  exact r.property.2

lemma sphereKernel_abs_le_one (r s : Time) : |sphereKernel r s|≤1 := by
  rw [abs_of_nonneg (sphereKernel_nonneg r s)]
  unfold sphereKernel
  have := min_le_left (r:ℝ) (s:ℝ)
  have := mul_nonneg r.property.1 s.property.1
  linarith [r.property.2]

lemma time_pospart_le_one (r s : Time) : |max ((s:ℝ)-r) 0|≤1 := by
  rw [abs_of_nonneg (le_max_right _ _),max_le_iff]
  exact ⟨by linarith [s.property.2,r.property.1],by norm_num⟩

lemma sphereKernel_tangent_algebra (r s t : Time)
    (h : UltrametricTriangle (r:ℝ) (s:ℝ) (t:ℝ)) (a : Time→ℝ) :
    a s*((t:ℝ)-(r:ℝ)*s)=sphereKernel r s*a s+a r*max ((t:ℝ)-r) 0 := by
  let A : ℝ→ℝ := fun x=>a (Set.projIcc 0 1 zero_le_one x)
  have he := ultrametric_tangent_algebra h A
  simp only [A,Set.projIcc_of_mem zero_le_one r.property,Set.projIcc_of_mem zero_le_one s.property,
    Subtype.coe_eta] at he
  have hm : (r:ℝ)-max ((r:ℝ)-s) 0=min (r:ℝ) (s:ℝ) := by
    rcases le_total (r:ℝ) (s:ℝ) with h|h
    · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h,sub_zero]
    · rw [max_eq_left (sub_nonneg.mpr h),min_eq_right h]; ring
  unfold sphereKernel
  rw [←hm]
  nlinarith only [he]

lemma sphereTail_pospart (ν : Measure Time) [IsProbabilityMeasure ν] (r : Time) :
    sphereTail ν r=1-(r:ℝ)-(∫ s,max ((s:ℝ)-r) 0 ∂ν) := by
  have hi := boundedAbs_integrable ν (fun s : Time=>max ((s:ℝ)-r) 0) (by fun_prop) 1 (time_pospart_le_one r)
  have he (s : Time) : 1-max (r:ℝ) (s:ℝ)=1-(r:ℝ)-max ((s:ℝ)-r) 0 := by
    rcases le_total (r:ℝ) (s:ℝ) with h|h
    · rw [max_eq_right h,max_eq_left (sub_nonneg.mpr h)]; ring
    · rw [max_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_zero]
  simp_rw [sphereTail,he]
  rw [integral_sub (integrable_const _) hi,integral_const]
  simp

lemma compact_test_smooth_approx {a b : ℝ} (hab : a≤b) (F : Icc a b→ᵇℝ)
    {ε : ℝ} (hε : 0<ε) :
    ∃ G : ℝ→ᵇℝ, ContDiff ℝ ∞ (G : ℝ→ℝ) ∧ ∀ r : Icc a b,|G r.val-F r|≤ε := by
  let f : ℝ→ℝ := fun x=>F (Set.projIcc a b hab x)
  have hu : UniformContinuous f :=
    (CompactSpace.uniformContinuous_of_continuous F.continuous).comp (LipschitzWith.projIcc hab).uniformContinuous
  obtain ⟨g,hg,hgb⟩ := hu.exists_contDiff_dist_le hε
  have hb (x : ℝ) : |g x|≤ε+‖F‖ := by
    have he := (hgb x).le
    rw [Real.dist_eq] at he
    have := F.norm_coe_le_norm (Set.projIcc a b hab x)
    change |f x|≤‖F‖ at this
    calc
      |g x|=|g x-f x+f x| := by rw [sub_add_cancel]
      _ ≤ |g x-f x|+|f x| := abs_add_le _ _
      _ ≤ ε+‖F‖ := add_le_add he this
  let G : ℝ→ᵇℝ := BoundedContinuousFunction.mkOfBound ⟨g,hg.continuous⟩ (2*(ε+‖F‖)) (by
    intro x y
    change dist (g x) (g y)≤_
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hb x,hb y]))
  refine ⟨G,hg,fun r => ?_⟩
  change |g r.val-F r|≤ε
  have he := (hgb r.val).le
  simpa only [Real.dist_eq,f,Set.projIcc_of_mem hab r.property,Subtype.coe_eta] using he

lemma smooth_compact_test_extend {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {a b : ℝ} (hab : a≤b)
    (p : Ω→Icc a b) (hp : Measurable p) (Z : Ω→ℝ) (hZ : Measurable Z)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x,|Z x|≤C)
    (hz : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→(∫ x,G (p x).val*Z x ∂P)=0)
    (F : Icc a b→ᵇℝ) : (∫ x,F (p x)*Z x ∂P)=0 := by
  have hFi : Integrable (fun x=>F (p x)*Z x) P :=
    Integrable.of_bound ((F.measurable.comp hp).mul hZ).aestronglyMeasurable (‖F‖*C)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (hb _) (abs_nonneg _) (norm_nonneg F))
  apply abs_nonpos_iff.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(C+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨G,hG,hGF⟩ := compact_test_smooth_approx hab F hδ
  have hGi : Integrable (fun x=>G (p x).val*Z x) P :=
    Integrable.of_bound ((G.measurable.comp (measurable_subtype_coe.comp hp)).mul hZ).aestronglyMeasurable (‖G‖*C)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (G.norm_coe_le_norm _) (hb _) (abs_nonneg _) (norm_nonneg G))
  have he : (∫ x,F (p x)*Z x ∂P)=(∫ x,(F (p x)-G (p x).val)*Z x ∂P) := by
    simp_rw [sub_mul]
    rw [integral_sub hFi hGi,hz G (hG.of_le (by norm_num)),sub_zero]
  rw [he]
  have hb' : ∀ x,‖(F (p x)-G (p x).val)*Z x‖≤δ*C := by
    intro x
    rw [Real.norm_eq_abs,abs_mul,abs_sub_comm]
    exact mul_le_mul (hGF _) (hb _) (abs_nonneg _) hδ.le
  have hi := norm_integral_le_of_norm_le_const (ae_of_all P hb')
  simp [Real.norm_eq_abs,Measure.real] at hi
  have hd : δ*(C+1)=ε := div_mul_cancel₀ ε (by linarith)
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory Set ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ContDiff

lemma bounded_continuous_test_extend {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P] (p : Ω→E) (hp : Measurable p)
    (Z : Ω→ℝ) (hZ : Measurable Z) {C : ℝ} (hC : 0≤C) (hb : ∀ x,|Z x|≤C)
    (hz : ∀ F : E→ᵇℝ,(∫ x,F (p x)*Z x ∂P)=0)
    (a : E→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (haB : ∀ r,|a r|≤A) :
    (∫ x,a (p x)*Z x ∂P)=0 := by
  have hmap : MeasurePreserving p P (P.map p) := ⟨hp,rfl⟩
  have hai : Integrable a (P.map p) := Integrable.of_bound ha.aestronglyMeasurable A
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using haB x)
  have hap : Integrable (fun x => a (p x)*Z x) P :=
    Integrable.of_bound ((ha.comp hp).mul hZ).aestronglyMeasurable (A*C)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (haB _) (hb x) (abs_nonneg _) hA)
  have he : |∫ x,a (p x)*Z x ∂P|≤0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε/(C+1)
    have hδ : 0<δ := div_pos hε (by linarith)
    obtain ⟨F,hF,hFi⟩ := hai.exists_boundedContinuous_integral_sub_le hδ
    have hiF : Integrable (fun x => F (p x)*Z x) P :=
      Integrable.of_bound ((F.measurable.comp hp).mul hZ).aestronglyMeasurable (‖F‖*C)
        (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (hb x) (abs_nonneg _) (norm_nonneg F))
    have hdif : Integrable (fun x => a (p x)-F (p x)) P :=
      hmap.integrable_comp_of_integrable (hai.sub hFi)
    have hrep : (∫ x,a (p x)*Z x ∂P)=(∫ x,(a (p x)-F (p x))*Z x ∂P) := by
      simp_rw [sub_mul]
      rw [integral_sub hap hiF,hz F,sub_zero]
    have happrox : (∫ x,|a (p x)-F (p x)| ∂P)≤δ := by
      have hm := integral_map (μ := P) hp.aemeasurable ((ha.sub F.measurable).abs.aestronglyMeasurable)
      change (∫ x, |a x - F x| ∂P.map p) = (∫ x, |a (p x) - F (p x)| ∂P) at hm
      rw [←hm]
      simpa only [Real.norm_eq_abs] using hF
    have hbound : |∫ x,(a (p x)-F (p x))*Z x ∂P|≤(∫ x,|a (p x)-F (p x)| * C ∂P) := by
      rw [←Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hdif.abs.mul_const C)
      exact ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
    rw [hrep]
    refine hbound.trans ?_
    rw [integral_mul_const]
    have hmul := mul_le_mul_of_nonneg_right happrox hC
    have hc : δ*(C+1)=ε := div_mul_cancel₀ ε (by linarith)
    linarith
  exact abs_nonpos_iff.mp he

lemma marked_zero_variance {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P] (p : Ω→E) (hp : Measurable p)
    (b : Ω→ℝ) (hb : Measurable b) (a : E→ℝ) (ha : Measurable a)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B) (haB : ∀ r,|a r|≤A) (hbB : ∀ x,|b x|≤B)
    (hfirst : ∀ F : E→ᵇℝ,(∫ x,F (p x)*b x ∂P)=(∫ x,F (p x)*a (p x) ∂P))
    (hsecond : (∫ x,(b x)^2 ∂P)=(∫ x,(a (p x))^2 ∂P)) :
    ∀ᵐ x ∂P,b x=a (p x) := by
  let Z := fun x => b x-a (p x)
  have hZm : Measurable Z := hb.sub (ha.comp hp)
  have hZb (x) : |Z x|≤B+A := (abs_sub _ _).trans (add_le_add (hbB x) (haB _))
  have hi (F : E→ᵇℝ) : Integrable (fun x => F (p x)*b x) P :=
    Integrable.of_bound ((F.measurable.comp hp).mul hb).aestronglyMeasurable (‖F‖*B)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (hbB x) (abs_nonneg _) (norm_nonneg F))
  have hi' (F : E→ᵇℝ) : Integrable (fun x => F (p x)*a (p x)) P :=
    Integrable.of_bound ((F.measurable.comp hp).mul (ha.comp hp)).aestronglyMeasurable (‖F‖*A)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (haB _) (abs_nonneg _) (norm_nonneg F))
  have hz (F : E→ᵇℝ) : (∫ x,F (p x)*Z x ∂P)=0 := by
    simp only [Z,mul_sub]
    rw [integral_sub (hi F) (hi' F),hfirst F,sub_self]
  have hcross := bounded_continuous_test_extend P p hp Z hZm (add_nonneg hB hA) hZb hz a ha hA haB
  have hi2 : Integrable (fun x => (b x)^2) P :=
    Integrable.of_bound (hb.pow_const 2).aestronglyMeasurable (B^2)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hbB x) 2)
  have hi2' : Integrable (fun x => (a (p x))^2) P :=
    Integrable.of_bound ((ha.comp hp).pow_const 2).aestronglyMeasurable (A^2)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (haB _) 2)
  have hiZ : Integrable (fun x => a (p x)*Z x) P :=
    Integrable.of_bound ((ha.comp hp).mul hZm).aestronglyMeasurable (A*(B+A))
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (haB _) (hZb x) (abs_nonneg _) hA)
  have hiZ2 : Integrable (fun x => (Z x)^2) P :=
    Integrable.of_bound (hZm.pow_const 2).aestronglyMeasurable ((B+A)^2)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hZb x) 2)
  have hzero : (∫ x,(Z x)^2 ∂P)=0 := by
    have he (x) : (Z x)^2=(b x)^2-(a (p x))^2-2*(a (p x)*Z x) := by dsimp [Z]; ring
    simp_rw [he]
    rw [integral_sub (show Integrable (fun x => (b x)^2-(a (p x))^2) P from hi2.sub hi2') (hiZ.const_mul 2),integral_sub hi2 hi2',integral_const_mul,
      hsecond,hcross]
    ring
  have hh := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (Z x)) hiZ2).mp hzero
  filter_upwards [hh] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

lemma tangent_wronskian_test {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Time) [IsProbabilityMeasure ν]
    (r s t : Ω→Time) (hr : Measurable r) (hs : Measurable s) (ht : Measurable t)
    (hmarg : P.map r=ν)
    (hlaws : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (hlawt : P.map (fun x=>(r x,t x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (htri : ∀ᵐ x ∂P,UltrametricTriangle (r x:ℝ) (s x:ℝ) (t x:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,|a x|≤A)
    (G : ℝ→ᵇℝ) :
    (∫ x,G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2)+2*a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) ∂P)=
      ∫ x,G x*((x:ℝ)-a x*sphereTail ν x+∫ y,sphereKernel x y*a y ∂ν) ∂ν := by
  let H : Time×Time→ℝ := fun p=>G p.1*sphereKernel p.1 p.2*a p.2
  let J : Time×Time→ℝ := fun p=>G p.1*a p.1*max ((p.2:ℝ)-p.1) 0
  let B : Time→ℝ := fun x=>G x*((x:ℝ)-a x*(1-(x:ℝ)^2))
  have hH : Measurable H := by dsimp [H]; unfold sphereKernel; fun_prop
  have hJ : Measurable J := by dsimp [J]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hbH (p : Time×Time) : |H p|≤‖G‖*A := by
    dsimp [H]
    rw [abs_mul,abs_mul]
    have h := mul_le_mul (G.norm_coe_le_norm (p.1:ℝ)) (sphereKernel_abs_le_one p.1 p.2) (abs_nonneg _) (norm_nonneg G)
    simp only [mul_one] at h
    exact mul_le_mul h (hab _) (abs_nonneg _) (norm_nonneg G)
  have hbJ (p : Time×Time) : |J p|≤‖G‖*A := by
    dsimp [J]
    rw [abs_mul,abs_mul]
    have h := mul_le_mul (G.norm_coe_le_norm (p.1:ℝ)) (hab p.1) (abs_nonneg _) (norm_nonneg G)
    simpa only [mul_one,Real.norm_eq_abs] using mul_le_mul h (time_pospart_le_one p.1 p.2) (abs_nonneg _) (mul_nonneg (norm_nonneg G) hA)
  have hbB (x : Time) : |B x|≤‖G‖*(1+A) := by
    have hx : |1-(x:ℝ)^2|≤1 := by
      have hx2 : (x:ℝ)^2≤1 := by nlinarith [x.property.1,x.property.2]
      rw [abs_of_nonneg (sub_nonneg.mpr hx2)]
      nlinarith [sq_nonneg (x:ℝ)]
    have habx : |a x*(1-(x:ℝ)^2)|≤A := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (hab x) hx (abs_nonneg _) hA
    have hb := (abs_sub (x:ℝ) (a x*(1-(x:ℝ)^2))).trans (add_le_add (time_abs_le_one x) habx)
    exact (abs_mul _ _).le.trans (mul_le_mul (G.norm_coe_le_norm _) hb (abs_nonneg _) (norm_nonneg G))
  have hiHp := boundedAbs_integrable P (fun x=>H (r x,s x)) (hH.comp (hr.prodMk hs)) _ (fun x=>hbH _)
  have hiJp := boundedAbs_integrable P (fun x=>J (r x,t x)) (hJ.comp (hr.prodMk ht)) _ (fun x=>hbJ _)
  have hiBp := boundedAbs_integrable P (fun x=>B (r x)) (hB.comp hr) _ (fun x=>hbB _)
  have hiB := boundedAbs_integrable ν B hB _ hbB
  have hiH := boundedAbs_integrable (ν.prod ν) H hH _ hbH
  have hiJ := boundedAbs_integrable (ν.prod ν) J hJ _ hbJ
  have hiHd := boundedAbs_integrable ν (fun x=>H (x,x)) (hH.comp (measurable_id.prodMk measurable_id)) _ (fun x=>hbH _)
  have hiJd := boundedAbs_integrable ν (fun x=>J (x,x)) (hJ.comp (measurable_id.prodMk measurable_id)) _ (fun x=>hbJ _)
  have heH := two_edge_integral P ν r s hr hs hlaws H hH _ hbH
  have heJ := two_edge_integral P ν r t hr ht hlawt J hJ _ hbJ
  have heB : (∫ x,B (r x) ∂P)=∫ x,B x ∂ν := by
    rw [←hmarg,integral_map hr.aemeasurable hB.aestronglyMeasurable]
  have hiBH : Integrable (fun x=>B (r x)+2*H (r x,s x)) P := hiBp.add (hiHp.const_mul 2)
  have hiHC : Integrable (fun x=>(∫ y,H (x,y) ∂ν)+H (x,x)) ν := hiH.integral_prod_left.add hiHd
  have hiJC : Integrable (fun x=>(∫ y,J (x,y) ∂ν)+J (x,x)) ν := hiJ.integral_prod_left.add hiJd
  have hiBC : Integrable (fun x=>B x+((∫ y,H (x,y) ∂ν)+H (x,x))) ν := hiB.add hiHC
  calc
    _ = ∫ x,B (r x)+2*H (r x,s x)+2*J (r x,t x) ∂P := by
      apply integral_congr_ae
      filter_upwards [htri] with x hx
      have he := sphereKernel_tangent_algebra (r x) (s x) (t x) hx a
      dsimp [B,H,J]
      calc
        _ = G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2))+2*G (r x)*(a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) := by ring
        _ = _ := by rw [he]; ring
    _ = (∫ x,B x ∂ν)+(∫ x,(∫ y,H (x,y) ∂ν)+H (x,x) ∂ν)+
        (∫ x,(∫ y,J (x,y) ∂ν)+J (x,x) ∂ν) := by
      rw [integral_add hiBH (hiJp.const_mul 2),
        integral_add hiBp (hiHp.const_mul 2),integral_const_mul,integral_const_mul,
        heB,heH,heJ,integral_add hiH.integral_prod_left hiHd,
        integral_add hiJ.integral_prod_left hiJd]
      ring
    _ = _ := by
      rw [←integral_add hiB hiHC,
        ←integral_add hiBC hiJC]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [B,H,J]
      simp_rw [mul_assoc (G x),integral_const_mul]
      rw [sphereTail_pospart]
      simp only [sphereKernel,min_self,sub_self,max_self,mul_zero,add_zero]
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

lemma bulkPairLaw_overlap (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) (F : CompactOverlap→ᵇℝ) :
    (∫ p,F p.1 ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K)))=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(bulkGibbsArrayLaw n M f v : Measure _) := by
  let A : BulkPairRange K→ᵇℝ := F.compContinuous ⟨Prod.fst,continuous_fst⟩
  rw [show (∫ p,F p.1 ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K)))=(∫ p,A p ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K))) from rfl,
    bulkPairLaw_integral]
  let G : CompactBlock CompactOverlap 2→ᵇℝ := F.compContinuous ⟨fun Q=>Q 0 1,by fun_prop⟩
  have he := bulkGibbsArray_block n M f v 2 G
  change (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(bulkGibbsArrayLaw n M f v : Measure _))=_ at he
  rw [he]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) 2)
    funext x
    change F (bulkOverlap (x 1) (x 0))=F (bulkOverlap (x 0) (x 1))
    congr 1
    apply Subtype.ext
    exact real_inner_comm _ _

lemma compact_pair_zero_variance (K : ℝ) (hK : 0≤K)
    (μ : ProbabilityMeasure (BulkPairRange K)) (ν : ProbabilityMeasure CompactOverlap)
    (a : ℝ→ℝ) (ha : Measurable a) (A : ℝ) (hA : 0≤A) (hb : ∀ r,|a r|≤A)
    (hmarg : (μ : Measure (BulkPairRange K)).map Prod.fst=(ν : Measure CompactOverlap))
    (hfirst : ∀ F : CompactOverlap→ᵇℝ,(∫ p,F p.1*p.2.val ∂(μ : Measure (BulkPairRange K)))=
      ∫ q,F q*a q.val ∂(ν : Measure CompactOverlap))
    (hsecond : (∫ p,p.2.val^2 ∂(μ : Measure (BulkPairRange K)))=(∫ q,(a q.val)^2 ∂(ν : Measure CompactOverlap))) :
    ∀ᵐ p ∂(μ : Measure (BulkPairRange K)),p.2.val=a p.1.val := by
  have hi (G : CompactOverlap→ℝ) (hG : Measurable G) :
      (∫ q,G q ∂(ν : Measure CompactOverlap))=(∫ p,G p.1 ∂(μ : Measure (BulkPairRange K))) := by
    rw [←hmarg]
    exact integral_map measurable_fst.aemeasurable hG.aestronglyMeasurable
  apply marked_zero_variance (μ : Measure (BulkPairRange K)) Prod.fst measurable_fst (fun p => p.2.val)
    (by fun_prop) (fun q => a q.val) (ha.comp measurable_subtype_coe) hA hK
    (fun r => hb r.val) (fun p => abs_le.mpr p.2.prop)
  · intro F
    rw [hfirst F]
    exact hi (fun q => F q*a q.val) (F.measurable.mul (ha.comp measurable_subtype_coe))
  · rw [hsecond]
    exact hi (fun q => (a q.val)^2) ((ha.comp measurable_subtype_coe).pow_const 2)


lemma compactPairMarginal_integral (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (F : CompactOverlap→ℝ) (hF : Measurable F) :
    (∫ r,F r ∂(compactPairMarginal ν : Measure CompactOverlap))=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _) :=
  integral_map (by exact (by fun_prop : Measurable (fun Q : CompactArray CompactOverlap => Q 0 1)).aemeasurable) hF.aestronglyMeasurable

lemma bulkPairLaw_limit_marginal (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (w : ℝ→ᵇℝ) (K : ℝ)
    (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖w‖^2≤K)
    (ν : ProbabilityMeasure (CompactArray CompactOverlap)) (μ : ProbabilityMeasure (BulkPairRange K))
    (hpair : Tendsto (fun n => bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n)) atTop (𝓝 μ))
    (hover : ∀ F : CompactOverlap→ᵇℝ,
      Tendsto (fun n => ∫ Q : CompactArray CompactOverlap,F (Q 0 1)
        ∂(bulkGibbsArrayLaw (s n) (M (s n)+2) g.f (v (s n)) : Measure _)) atTop
        (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _)))) :
    (μ : Measure (BulkPairRange K)).map Prod.fst=(compactPairMarginal ν : Measure CompactOverlap) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  let A : BulkPairRange K→ᵇℝ := F.compContinuous ⟨Prod.fst,continuous_fst⟩
  have he := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hpair
  change Tendsto (fun n => ∫ p,F p.1 ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))
    atTop (𝓝 (∫ p,F p.1 ∂(μ : Measure (BulkPairRange K)))) at he
  simp_rw [bulkPairLaw_overlap] at he
  have hi := integral_map (μ:=(μ : Measure (BulkPairRange K))) measurable_fst.aemeasurable F.measurable.aestronglyMeasurable
  change (∫ r,F r ∂(μ : Measure (BulkPairRange K)).map Prod.fst)=(∫ p,F p.1 ∂(μ : Measure (BulkPairRange K))) at hi
  rw [hi,compactPairMarginal_integral ν F F.measurable]
  exact tendsto_nhds_unique he (hover F)

theorem bulkPairLaw_identification (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) (K : ℝ) (hK0 : 0≤K)
    (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖w‖^2≤K)
    (μ : ProbabilityMeasure (BulkPairRange K))
    (hpair : Tendsto (fun n => bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖w‖^2) ∧
      (μ : Measure (BulkPairRange K)).map Prod.fst=(compactPairMarginal ν : Measure CompactOverlap) ∧
      ∀ᵐ p ∂(μ : Measure (BulkPairRange K)),p.2.val=a p.1.val := by
  obtain ⟨a,ham,hab,ht⟩ := bulk_marked_empirical_limits M g v s hs α hd hlim hGG hgeo hn w
  have hmarg := bulkPairLaw_limit_marginal M g v s w K hK ν μ hpair
    (bulk_full_pair_tendsto M g v s hlim hGG hgeo hn)
  have htμ (F : C(BulkPairRange K,ℝ)) :
      Tendsto (fun n => ∫ p,F p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))
        atTop (𝓝 (∫ p,F p ∂(μ : Measure (BulkPairRange K)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (BoundedContinuousFunction.mkOfCompact F)).continuousAt.tendsto.comp hpair
  refine ⟨fun r => α*a r,ham.const_mul hα,fun r =>
    ⟨mul_nonneg hα (hab r).1,mul_le_mul_of_nonneg_left (hab r).2 hα⟩,hmarg,?_⟩
  apply compact_pair_zero_variance K hK0 μ (compactPairMarginal ν) (fun r => α*a r)
    (ham.measurable.const_mul α) (α*‖w‖^2) (mul_nonneg hα (sq_nonneg _))
    (fun r => by rw [abs_of_nonneg (mul_nonneg hα (hab r).1)]; exact mul_le_mul_of_nonneg_left (hab r).2 hα) hmarg
  · intro F
    let A : C(BulkPairRange K,ℝ) := ⟨fun p => F p.1*p.2.val,by fun_prop⟩
    have he := htμ A
    have htest n : (∫ p,A p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))=
        bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
          (fun d x => bulkPairOverlapTest (s n) F x*bulkPairAverage (s n) (M (s n)+2) w d x) :=
      bulkPairLaw_integral _ _ _ _ _ _ _ (BoundedContinuousFunction.mkOfCompact A)
    simp_rw [htest] at he
    have hvalue := tendsto_nhds_unique he (ht F).1
    change (∫ p,A p ∂(μ : Measure (BulkPairRange K)))=_
    rw [hvalue,compactPairMarginal_integral ν (fun q => F q*(α*a q.val)) (F.measurable.mul (ham.measurable.comp measurable_subtype_coe |>.const_mul α)),←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun Q => by ring
  · let A : C(BulkPairRange K,ℝ) := ⟨fun p => p.2.val^2,by fun_prop⟩
    have he := htμ A
    have htest n : (∫ p,A p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))=
        bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
          (fun d x => bulkPairOverlapTest (s n) 1 x*(bulkPairAverage (s n) (M (s n)+2) w d x)^2) := by
      have hi := bulkPairLaw_integral (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) (BoundedContinuousFunction.mkOfCompact A)
      change (∫ p,A p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))=
        bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
          (fun d x => (bulkPairAverage (s n) (M (s n)+2) w d x)^2) at hi
      simpa only [bulkPairOverlapTest,BoundedContinuousFunction.coe_one,Pi.one_apply,one_mul] using hi
    simp_rw [htest] at he
    have hvalue := tendsto_nhds_unique he (ht 1).2
    change (∫ p,A p ∂(μ : Measure (BulkPairRange K)))=_
    rw [hvalue,compactPairMarginal_integral ν (fun q => (α*a q.val)^2) ((ham.measurable.comp measurable_subtype_coe |>.const_mul α).pow_const 2),←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun Q => by simp; ring

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

theorem bulkMarkedArray_identification (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hmarked : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ a : ℝ→ℝ,Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖g.d1‖^2) ∧
      (μ : Measure (CompactArray (BulkPairRange K))).map (fun Q => (Q 1 0).1)=
        (compactPairMarginal ν : Measure CompactOverlap) ∧
      ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val := by
  have hc : Continuous (fun Q : CompactArray (BulkPairRange K)=>Q 1 0) := by fun_prop
  let ρ := μ.map hc.measurable.aemeasurable
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hmarked hc
  change Tendsto (fun n => (bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)).map hc.measurable.aemeasurable) atTop (𝓝 ρ) at ht
  simp_rw [bulkMarkedArray_pair] at ht
  obtain ⟨a,ham,hab,hmarg,hgraph⟩ := bulkPairLaw_identification M g v s hs α hα hd ν hlim hGG hgeo hn g.d1 K hK0 hK ρ ht
  refine ⟨a,ham,hab,?_,?_⟩
  · change (Measure.map Prod.fst (Measure.map (fun Q : CompactArray (BulkPairRange K)=>Q 1 0) (μ : Measure _)))=_ at hmarg
    rwa [Measure.map_map measurable_fst hc.measurable] at hmarg
  · apply compact_exchangeable_offdiag_ae μ
      (fun e => compact_exchangeability_limit hmarked e (fun n => bulkMarkedArray_exchangeable (s n) (M (s n)+2) g (v (s n)) K (hK n) e))
      (fun p => p.2.val=a p.1.val)
    exact ae_of_ae_map hc.measurable.aemeasurable hgraph

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TangentConsistency
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

lemma sphereTail_measurable (ν : Measure Time) [IsProbabilityMeasure ν] :
    Measurable (sphereTail ν) := by
  have hm : Measurable (fun p : Time×Time=>1-max (p.1:ℝ) (p.2:ℝ)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma sphereKernel_integral_measurable (ν : Measure Time) [IsProbabilityMeasure ν]
    (a : Time→ℝ) (ha : Measurable a) :
    Measurable (fun x=>∫ y,sphereKernel x y*a y ∂ν) := by
  have hm : Measurable (fun p : Time×Time=>sphereKernel p.1 p.2*a p.2) := by
    unfold sphereKernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma sphereKernel_integral_abs_bound (ν : Measure Time) [IsProbabilityMeasure ν]
    (a : Time→ℝ) {A : ℝ} (_hA : 0≤A) (hab : ∀ x,|a x|≤A) (r : Time) :
    |∫ y,sphereKernel r y*a y ∂ν|≤A := by
  have hb (y : Time) : ‖sphereKernel r y*a y‖≤A := by
    rw [Real.norm_eq_abs,abs_mul]
    simpa only [one_mul] using mul_le_mul (sphereKernel_abs_le_one r y) (hab y) (abs_nonneg _) zero_le_one
  simpa [Real.norm_eq_abs,Measure.real] using
    norm_integral_le_of_norm_le_const (ae_of_all ν hb)

lemma tangent_wronskian_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Time) [IsProbabilityMeasure ν]
    (r s t : Ω→Time) (hr : Measurable r) (hs : Measurable s) (ht : Measurable t)
    (hmarg : P.map r=ν)
    (hlaws : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (hlawt : P.map (fun x=>(r x,t x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (htri : ∀ᵐ x ∂P,UltrametricTriangle (r x:ℝ) (s x:ℝ) (t x:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,|a x|≤A)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ x,G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2)+2*a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) ∂P)=0) :
    ∀ᵐ x ∂ν,a x*sphereTail ν x=(x:ℝ)+∫ y,sphereKernel x y*a y ∂ν := by
  let Z : Time→ℝ := fun x=>(x:ℝ)-a x*sphereTail ν x+∫ y,sphereKernel x y*a y ∂ν
  have hZm : Measurable Z := (measurable_subtype_coe.sub (ha.mul (sphereTail_measurable ν))).add
    (sphereKernel_integral_measurable ν a ha)
  have hZb (x : Time) : |Z x|≤1+2*A := by
    have htail : |sphereTail ν x|≤1 := by
      rw [abs_of_nonneg (sphereTail_nonneg ν x)]
      exact (sphereTail_upper ν x).trans (by linarith [x.property.1])
    have hx : |a x*sphereTail ν x|≤A := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (hab x) htail (abs_nonneg _) hA
    have hg := (abs_sub (x:ℝ) (a x*sphereTail ν x)).trans (add_le_add (time_abs_le_one x) hx)
    exact (abs_add_le _ _).trans ((add_le_add hg (sphereKernel_integral_abs_bound ν a hA hab x)).trans (by ring_nf; exact le_rfl))
  have hz : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→(∫ x,G x*Z x ∂ν)=0 := by
    intro G hG
    rw [←tangent_wronskian_test P ν r s t hr hs ht hmarg hlaws hlawt htri a ha hA hab G]
    exact hT G hG
  have hz' (F : Time→ᵇℝ) : (∫ x,F x*Z x ∂ν)=0 :=
    smooth_compact_test_extend ν zero_le_one id measurable_id Z hZm (by linarith) hZb hz F
  have hz2 := bounded_continuous_test_extend ν id measurable_id Z hZm (by linarith) hZb hz' Z hZm (by linarith) hZb
  have hi : Integrable (fun x=>Z x*Z x) ν := boundedAbs_integrable ν _ (hZm.mul hZm) ((1+2*A)^2) (fun x=>by
    rw [abs_mul,←pow_two]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZb x) 2)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x=>mul_self_nonneg (Z x)) hi).mp hz2
  filter_upwards [hae] with x hx
  have h := mul_self_eq_zero.mp hx
  change (x:ℝ)-a x*sphereTail ν x+∫ y,sphereKernel x y*a y ∂ν=0 at h
  linarith

theorem tangent_sphere_self_consistency {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Time) [IsProbabilityMeasure ν]
    (r s t : Ω→Time) (hr : Measurable r) (hs : Measurable s) (ht : Measurable t)
    (hmarg : P.map r=ν)
    (hlaws : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (hlawt : P.map (fun x=>(r x,t x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (htri : ∀ᵐ x ∂P,UltrametricTriangle (r x:ℝ) (s x:ℝ) (t x:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,0≤a x ∧ a x≤A)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ x,G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2)+2*a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) ∂P)=0) :
    (∀ᵐ x ∂ν,a x=∫ y in 0..(x:ℝ),(realTail ν y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂ν,(x:ℝ)≤A/(1+A) := by
  apply sphere_self_consistency ν hA ha.aestronglyMeasurable
    (ae_of_all _ fun x=>(hab x).1) (ae_of_all _ fun x=>(hab x).2)
  exact tangent_wronskian_ae P ν r s t hr hs ht hmarg hlaws hlawt htri a ha hA
    (fun x=>by rw [abs_of_nonneg (hab x).1]; exact (hab x).2) hT

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayTangentConsistency
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

lemma compact_other_edge_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (F : CompactBlock K 2→ᵇℝ) (g : K→ᵇℝ),compactGGDefect μ 2 0 F g=0)
    (he : MeasurePreserving (compactRelabel (K:=K) (Equiv.swap 0 1)) (μ : Measure _) (μ : Measure _))
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray K)),Q 1 0=Q 0 1) :
    (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 1 2))=
      (1/2:ℝ≥0) • (((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)))+
      (1/2:ℝ≥0) • ((μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 1))) := by
  have h := congrArg (Measure.map (fun Q : CompactArray K=>(Q 0 1,Q 0 2))) he.map_eq
  rw [Measure.map_map (by fun_prop) he.measurable] at h
  have h' : (μ : Measure (CompactArray K)).map (fun Q=>(Q 1 0,Q 1 2))=
      (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 2)) := by
    simpa [Function.comp_def,compactRelabel,Equiv.swap_apply_def] using h
  have hm : (μ : Measure (CompactArray K)).map (fun Q=>(Q 1 0,Q 1 2))=
      (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 1 2)) :=
    Measure.map_congr (hsy.mono (fun Q hQ=>by dsimp only; rw [hQ]))
  rw [←hm,h',compact_two_edge_law μ hGG]

lemma array_tangent_self_consistency (μ : ProbabilityMeasure (CompactArray Time))
    (hGG : ∀ (F : CompactBlock Time 2→ᵇℝ) (g : Time→ᵇℝ),compactGGDefect μ 2 0 F g=0)
    (he : MeasurePreserving (compactRelabel (K:=Time) (Equiv.swap 0 1)) (μ : Measure _) (μ : Measure _))
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),∀ i j,Q i j=Q j i)
    (hul : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),∀ i j k,min (Q i j:ℝ) (Q i k:ℝ)≤(Q j k:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,0≤a x ∧ a x≤A)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ Q : CompactArray Time,G (Q 0 1)*((Q 0 1:ℝ)-a (Q 0 1)*(1-(Q 0 1:ℝ)^2)+
        2*a (Q 0 2)*((Q 1 2:ℝ)-(Q 0 1:ℝ)*(Q 0 2:ℝ))) ∂(μ : Measure _))=0) :
    (∀ᵐ x : Time ∂((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
      a x=∫ y in 0..(x:ℝ),(realTail ((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)) y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),(x:ℝ)≤A/(1+A) := by
  let ν := (μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by first | fun_prop | exact (measurable_pi_apply 1).comp (measurable_pi_apply 0)))
  have hd : ν.map (fun x=>(x,x))=(μ : Measure (CompactArray Time)).map (fun Q=>(Q 0 1,Q 0 1)) := by
    change ((μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)).map (fun x=>(x,x))=_
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  apply tangent_sphere_self_consistency (μ : Measure (CompactArray Time)) ν (fun Q=>Q 0 1) (fun Q=>Q 0 2) (fun Q=>Q 1 2)
    (by fun_prop) (by fun_prop) (by fun_prop) rfl
    (by rw [hd]; exact compact_two_edge_law μ hGG)
    (by rw [hd]; exact compact_other_edge_law μ hGG he (hsy.mono (fun Q hQ=>hQ 1 0)))
    _ a ha hA hab hT
  filter_upwards [hsy,hul] with Q hS hU
  refine ⟨hU 0 1 2,?_,?_⟩
  · have h := hU 1 0 2
    simpa only [hS 1 0] using h
  · have h := hU 2 0 1
    simpa only [hS 2 0,hS 2 1] using h

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

lemma marked_tangent_canonical (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=BulkPairRange K) e) (μ : Measure _) (μ : Measure _))
    (a : ℝ→ℝ)
    (hgraph : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val)
    (G : ℝ→ᵇℝ)
    (hT : (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0) :
    (∫ Q : CompactArray (BulkPairRange K),G (Q 0 1).1.val*((Q 0 1).1.val-a (Q 0 1).1.val*(1-(Q 0 1).1.val^2)+
      2*a (Q 0 2).1.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val)) ∂(μ : Measure _))=0 := by
  let F1 := (markedTangentR K G).compContinuous ⟨compactBlock 2,compactBlock_continuous 2⟩
  let F2 := (markedTangentPair K G).compContinuous ⟨compactBlock 2,compactBlock_continuous 2⟩
  let F3 := (markedTangentTriple K G).compContinuous ⟨compactBlock 3,compactBlock_continuous 3⟩
  let F4 : CompactArray (BulkPairRange K)→ᵇℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun Q=>G (Q 0 1).1.val*(Q 0 2).2.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val),by fun_prop⟩
  let e : Equiv.Perm ℕ := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  have hp : (∫ Q,F3 Q ∂(μ : Measure _))=∫ Q,F4 Q ∂(μ : Measure _) := by
    have h := integral_map (μ:=(μ : Measure (CompactArray (BulkPairRange K)))) (he e).measurable.aemeasurable F3.measurable.aestronglyMeasurable
    rw [(he e).map_eq] at h
    change (∫ Q,F3 Q ∂(μ : Measure _))=∫ Q,F3 (compactRelabel e Q) ∂(μ : Measure _) at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [] with Q
    simp [F3,F4,markedTangentTriple,compactBlock,compactRelabel,e,Equiv.swap_apply_def]
  have hi1 := F1.integrable (μ : Measure _)
  have hi2 := F2.integrable (μ : Measure _)
  have hi4 := F4.integrable (μ : Measure _)
  have hi12 : Integrable (fun Q=>F1 Q-F2 Q) (μ : Measure _) := hi1.sub hi2
  have hz : (∫ Q,(F1 Q-F2 Q)+2*F4 Q ∂(μ : Measure _))=0 := by
    rw [integral_add hi12 (hi4.const_mul 2),integral_sub hi1 hi2,integral_const_mul,←hp]
    exact hT
  rw [←hz]
  apply integral_congr_ae
  filter_upwards [hgraph] with Q hQ
  have h01 := hQ 0 1 (by omega)
  have h02 := hQ 0 2 (by omega)
  change G (Q 0 1).1.val*((Q 0 1).1.val-a (Q 0 1).1.val*(1-(Q 0 1).1.val^2)+
    2*a (Q 0 2).1.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val))=
    ((Q 0 1).1.val*G (Q 0 1).1.val-G (Q 0 1).1.val*(Q 0 1).2.val*(1-(Q 0 1).1.val^2))+
      2*(G (Q 0 1).1.val*(Q 0 2).2.val*((Q 1 2).1.val-(Q 0 1).1.val*(Q 0 2).1.val))
  rw [h01,h02]
  ring

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

lemma marked_time_self_consistency (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=BulkPairRange K) e) (μ : Measure _) (μ : Measure _))
    (hGG : ∀ n (i : Fin n) (F : CompactBlock CompactOverlap n→ᵇℝ) (g : CompactOverlap→ᵇℝ),
      compactGGDefect (compactMapLaw Prod.fst continuous_fst μ) n i F g=0)
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).1=(Q j i).1)
    (hul : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j k,
      min (Q i j).1.val (Q i k).1.val≤(Q j k).1.val)
    (hn : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,0≤(Q i j).1.val)
    (a : ℝ→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,0≤a x ∧ a x≤A)
    (hgraph : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0) :
    let ν := (markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)
    (∀ᵐ x : Time ∂ν,a x=∫ y in 0..(x:ℝ),(realTail ν y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂ν,(x:ℝ)≤A/(1+A) := by
  let e : BulkPairRange K→Time := fun p=>nonnegativeSpinTime p.1
  have hec : Continuous e := nonnegativeSpinTime_continuous.comp continuous_fst
  have hm : Measurable (compactMapArray e) := (compactMapArray_continuous hec).measurable
  have hs : ∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),∀ i j,Q i j=Q j i := by
    apply (ae_map_iff hm.aemeasurable (by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i=>MeasurableSet.iInter fun j=>measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
    filter_upwards [hsy] with Q hQ
    intro i j
    exact congrArg nonnegativeSpinTime (hQ i j)
  have hu : ∀ᵐ Q ∂(markedTimeLaw K μ : Measure (CompactArray Time)),∀ i j k,min (Q i j:ℝ) (Q i k:ℝ)≤(Q j k:ℝ) := by
    apply (ae_map_iff hm.aemeasurable (by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i=>MeasurableSet.iInter fun j=>MeasurableSet.iInter fun k=>
        measurableSet_le (by fun_prop) (by fun_prop))).mpr
    filter_upwards [hul,hn] with Q hQ hN
    intro i j k
    simpa only [compactMapArray,e,nonnegativeSpinTime_val (hN i j),nonnegativeSpinTime_val (hN i k),
      nonnegativeSpinTime_val (hN j k)] using hQ i j k
  apply array_tangent_self_consistency (markedTimeLaw K μ)
    (by rw [markedTimeLaw_factor]; exact compactMapLaw_gg _ _ _ hGG 2 0)
    (compactMapLaw_exchangeable e hec μ (Equiv.swap 0 1) (he _)) hs hu
    (fun x=>a x.val) (ha.comp measurable_subtype_coe) hA (fun x=>hab x.val)
  intro G hG
  rw [show (markedTimeLaw K μ : Measure (CompactArray Time))=(μ : Measure _).map (compactMapArray e) from rfl,
    integral_map hm.aemeasurable (show AEStronglyMeasurable (fun Q : CompactArray Time=>G (Q 0 1)*
      ((Q 0 1:ℝ)-a (Q 0 1)*(1-(Q 0 1:ℝ)^2)+2*a (Q 0 2)*((Q 1 2:ℝ)-(Q 0 1:ℝ)*(Q 0 2:ℝ)))) _ from (show Measurable (fun Q : CompactArray Time=>G (Q 0 1)*
      ((Q 0 1:ℝ)-a (Q 0 1)*(1-(Q 0 1:ℝ)^2)+2*a (Q 0 2)*((Q 1 2:ℝ)-(Q 0 1:ℝ)*(Q 0 2:ℝ)))) from by fun_prop).aestronglyMeasurable)]
  rw [←marked_tangent_canonical K μ he a hgraph G (hT G hG)]
  apply integral_congr_ae
  filter_upwards [hn] with Q hN
  simp only [compactMapArray,e,nonnegativeSpinTime_val (hN 0 1),nonnegativeSpinTime_val (hN 0 2),nonnegativeSpinTime_val (hN 1 2)]

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

theorem bulk_marked_self_consistency_oai (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ)
    (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
    (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ a : ℝ→ℝ,Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖g.d1‖^2) ∧
      (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val) ∧
      (∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
        a x=∫ y in 0..(x:ℝ),(realTail ((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)) y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
        (x:ℝ)≤(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2) := by
  have hOm := bulk_limit_geometry M g.f v (Eventually.of_forall hv) hdO hs ho
  obtain ⟨a,ham,hab,_,hag⟩ := bulkMarkedArray_identification M g v s hs.tendsto_atTop α hα hd ν ho
    hOm.2.2 hOm.1 hOm.2.1 K hK0 hK μ hf
  have hf' := bulkMarkedArray_limit_overlap (fun n=>M n+2) g v s K hK hf
  have hFm := bulk_limit_geometry (fun n=>M n+2) g.f v (Eventually.of_forall hv) hdF hs hf'
  have he (e : Equiv.Perm ℕ) := compact_exchangeability_limit hf e
    (fun n=>bulkMarkedArray_exchangeable (s n) (M (s n)+2) g (v (s n)) K (hK n) e)
  have hGm := marked_overlap_geometry K μ he hFm.1 hFm.2.1
  have hsc := marked_time_self_consistency K μ he
    (bulk_limit_gg (fun n=>M n+2) g.f v (Eventually.of_forall hv) hdF hs hf')
    hGm.1 hGm.2.1 hGm.2.2 a ham.measurable (mul_nonneg hα (sq_nonneg _)) hab hag
    (fun G hG=>bulk_marked_tangent_limit (fun n=>M n+2) g v hC hvC K hs hK μ hf G hG)
  exact ⟨a,ham,hab,hag,hsc.1,hsc.2⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency_oai := @OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency_oai
