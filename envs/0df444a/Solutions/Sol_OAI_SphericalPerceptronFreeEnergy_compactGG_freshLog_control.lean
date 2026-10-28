-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:33:46.33589+00:00
-- url     : https://prove2.me/submissions/68e6c2cf-309d-4cb5-959c-8b7399bd5403

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_labelProfile_reference_full_exists

section
-- module Solutions.OAIQ061_PF.Compat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

open TopologicalSpace

lemma compact_array_law_subsequence {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [CompactSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ℕ → ProbabilityMeasure (CompactArray K)) :
    ∃ ν : ProbabilityMeasure (CompactArray K), ∃ s : ℕ → ℕ,
      StrictMono s ∧ Tendsto (μ ∘ s) atTop (𝓝 ν) := by
  obtain ⟨ν, -, s, hs, hμ⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  exact ⟨ν,s,hs,hμ⟩

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

lemma compactGGDefect_continuous {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    Continuous (fun μ : ProbabilityMeasure (CompactArray K) => compactGGDefect μ n i f g) := by
  let f' : CompactArray K →ᵇ ℝ := f.compContinuous ⟨compactBlock n,compactBlock_continuous n⟩
  let g' (i j : ℕ) : CompactArray K →ᵇ ℝ := g.compContinuous ⟨fun Q => Q i j,by fun_prop⟩
  have hf := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f'
  have hg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (g' i j)
  have hfg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f' * g' i j)
  exact (continuous_const.mul (hfg i n) |>.sub (hf.mul (hg 0 1))).sub
    (continuous_finsetSum _ fun j _ => hfg i j)

lemma compactGGDefect_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] {μ : ℕ → ProbabilityMeasure (CompactArray K)}
    {ν : ProbabilityMeasure (CompactArray K)} (hμ : Tendsto μ atTop (𝓝 ν))
    (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ)
    (hdef : Tendsto (fun k => compactGGDefect (μ k) n i f g) atTop (𝓝 0)) :
    compactGGDefect ν n i f g = 0 :=
  tendsto_nhds_unique ((compactGGDefect_continuous n i f g).continuousAt.tendsto.comp hμ) hdef

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

lemma integral_continuous_tendsto_of_moments {a b : ℝ}
    (μ : ℕ → Measure (Icc a b)) (ν : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ x, (x.val)^k ∂μ n) atTop
      (𝓝 (∫ x, (x.val)^k ∂ν))) (f : C(Icc a b, ℝ)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hi (ρ : Measure (Icc a b)) [IsFiniteMeasure ρ] (p : ℝ[X]) :
      Integrable (fun x : Icc a b => p.eval x.val) ρ :=
    (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (p : ℝ[X]) : Tendsto (fun n => ∫ x, p.eval x.val ∂μ n) atTop
      (𝓝 (∫ x, p.eval x.val ∂ν)) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add,integral_add (hi _ p) (hi _ q)] using hp.add hq
    | monomial k c =>
      simpa only [Polynomial.eval_monomial,integral_const_mul] using tendsto_const_nhds.mul (h k)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨p, hpε⟩ := exists_polynomial_near_continuousMap a b f (ε/3) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hp p)) (ε/3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbnd (ρ : Measure (Icc a b)) [IsProbabilityMeasure ρ] :
      |(∫ x, p.eval x.val ∂ρ) - ∫ x, f x ∂ρ| < ε/3 := by
    rw [← integral_sub (hi ρ p) (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    · calc
        |∫ x, p.eval x.val - f x ∂ρ| ≤ ‖p.toContinuousMapOn (Icc a b)-f‖ := by
          simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs,ContinuousMap.sub_apply,Polynomial.toContinuousMapOn_apply,Polynomial.toContinuousMap_apply] using
            (norm_integral_le_of_norm_le_const (μ := ρ)
              (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm
                (p.toContinuousMapOn (Icc a b)-f) x))
        _ < ε/3 := hpε
  have h₁ := hbnd (μ n)
  have h₂ := hbnd ν
  have h₃ := hN n hn
  rw [Real.dist_eq] at h₃ ⊢
  calc
    |(∫ x, f x ∂μ n) - ∫ x, f x ∂ν| ≤
        |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
        |(∫ x, p.eval x.val ∂μ n) - ∫ x, p.eval x.val ∂ν| +
        |(∫ x, p.eval x.val ∂ν) - ∫ x, f x ∂ν| := by
          calc
            _ ≤ |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
                |(∫ x, p.eval x.val ∂μ n) - ∫ x, f x ∂ν| := abs_sub_le _ _ _
            _ ≤ _ := by
              linarith [abs_sub_le (∫ x, p.eval x.val ∂μ n)
                (∫ x, p.eval x.val ∂ν) (∫ x, f x ∂ν)]
    _ < ε := by rw [abs_sub_comm (∫ x, f x ∂μ n)] ; linarith

lemma trial_integrable (m : Trial) : Integrable m timeLaw := by
  change Integrable m (volume : Measure Time)
  apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (m.nonneg t)]
    exact m.le_one t

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

theorem progressive_zero (P : Measure BrownianPath) :
    Progressive P (fun _ _ => 0) := by
  intro t
  exact measurable_const

theorem abs_integral_reward_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (X : BrownianPath → ℝ) :
    |∫ ω, f (X ω) ∂P| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun ω => f (X ω)) (C := ‖f‖)
    (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X ω))
  simpa using h

theorem controlPayoff_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (v : Time → BrownianPath → ℝ) :
    controlPayoff P f m v ≤ ‖f‖ := by
  unfold controlPayoff
  have h := (abs_integral_reward_le P f
    (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))
  have h := (le_abs_self _).trans h
  exact (sub_le_self _ (div_nonneg ENNReal.toReal_nonneg (by norm_num))).trans h

theorem controlPayoffs_nonempty (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}.Nonempty := by
  exact ⟨_, fun _ _ => 0, progressive_zero P, by simp, rfl⟩

theorem controlPayoffs_bddAbove (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    BddAbove {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v} := by
  refine ⟨‖f‖, ?_⟩
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlDrift
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma brownianEval_measurable (t : ℝ≥0) : Measurable (brownianEval t) :=
  (continuous_eval_const t).measurable

lemma usualBrownianSigma_le_completion (P : Measure BrownianPath) (t : Time) :
    usualBrownianSigma P t ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) := by
  unfold usualBrownianSigma
  refine (iInf_le _ (⟨2, lt_of_le_of_lt t.property.2 (by norm_num)⟩ :
    {s : ℝ≥0 // (t : ℝ) < s})).trans ?_
  apply sup_le
  · apply iSup_le
    intro r
    exact (brownianEval_measurable r.val).comap_le.trans
      (fun _ hs => hs.nullMeasurableSet)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact NullMeasurableSet.of_null hs

lemma progressive_joint_complete (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    Measurable (fun p : Time × NullMeasurableSpace BrownianPath P => v p.1 p.2) := by
  have h := (hv 1).mono (show MeasurableSpace.prod inferInstance (usualBrownianSigma P 1) ≤
      MeasurableSpace.prod inferInstance
        (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) from
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (usualBrownianSigma_le_completion P 1))) le_rfl
  have hf : Measurable (fun p : Time × NullMeasurableSpace BrownianPath P =>
      (⟨p.1, p.1.property.2⟩ : Set.Iic (1 : Time))) := measurable_fst.subtype_mk
  exact h.comp (hf.prodMk measurable_snd)

lemma progressive_time_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (ω : BrownianPath) :
    Measurable (fun t : Time => v t ω) :=
  (progressive_joint_complete P hv).comp (measurable_id.prodMk measurable_const)

lemma controlDrift_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (controlDrift m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => controlDrift m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      (progressive_joint_complete P hv)).stronglyMeasurable.integral_prod_left'.measurable
  exact (show NullMeasurable (controlDrift m v) P from h).aemeasurable

lemma pathControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (pathControlCost m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => pathControlCost m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      ((progressive_joint_complete P hv).pow_const 2)).ennreal_ofReal.lintegral_prod_left'
  exact (show NullMeasurable (pathControlCost m v) P from h).aemeasurable

lemma controlledTerminal_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (fun ω => brownianEval 1 ω + controlDrift m v ω) P :=
  (brownianEval_measurable 1).aemeasurable.add (controlDrift_aemeasurable P m hv)

lemma controlReward_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) :
    Integrable (fun ω => f (brownianEval 1 ω + controlDrift m v ω)) P := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.measurable.comp_aemeasurable
      (controlledTerminal_aemeasurable P m hv)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalVariational
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma indep_eventuallyMeasurable_left {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) {m n : MeasurableSpace Ω} (h : Indep m n μ) :
    Indep (eventuallyMeasurableSpace m (ae μ)) n μ := by
  rw [Indep_iff] at h ⊢
  rintro A B ⟨A', hA', hAA'⟩ hB
  rw [measure_congr (hAA'.inter (Filter.EventuallyEq.refl (ae μ) B)), measure_congr hAA']
  exact h A' B hA' hB

lemma nullSigma_le_eventuallyMeasurable (P : Measure BrownianPath)
    (m : MeasurableSpace BrownianPath) :
    nullSigma P ≤ eventuallyMeasurableSpace m (ae P) := by
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact ⟨∅, MeasurableSet.empty, ae_eq_empty.mpr hA⟩

lemma rawBrownianSigma_le_past_comap (s : ℝ≥0) :
    rawBrownianSigma s ≤
      MeasurableSpace.comap (fun ω (r : Set.Iic s) => brownianEval r.val ω) inferInstance := by
  apply iSup_le
  intro r
  rintro A ⟨B, hB, rfl⟩
  exact ⟨(fun f : Set.Iic s → ℝ => f r) ⁻¹' B, (measurable_pi_apply r) hB, rfl⟩

lemma usualBrownianSigma_le_ae_raw (P : Measure BrownianPath) (t : Time)
    (s : ℝ≥0) (hts : (t : ℝ) < s) :
    usualBrownianSigma P t ≤ eventuallyMeasurableSpace (rawBrownianSigma s) (ae P) := by
  apply (iInf_le _ (⟨s, hts⟩ : {s : ℝ≥0 // (t : ℝ) < s})).trans
  exact sup_le le_eventuallyMeasurableSpace (nullSigma_le_eventuallyMeasurable P _)

lemma brownian_future_indep_raw (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (s u : ℝ≥0) :
    Indep (rawBrownianSigma s)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P := by
  have h := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply u)
  exact indep_of_indep_of_le_left h (rawBrownianSigma_le_past_comap s)

lemma brownian_future_indep_usual_earlier (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (t : Time) (s u : ℝ≥0)
    (hts : (t : ℝ) < s) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P :=
  indep_of_indep_of_le_left
    (indep_eventuallyMeasurable_left P (brownian_future_indep_raw P hB s u))
    (usualBrownianSigma_le_ae_raw P t s hts)

lemma indep_setIntegral_eq_mul_null {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ} {A : Set Ω}
    (hI : Indep m (MeasurableSpace.comap X (borel ℝ)) P)
    (hX : AEMeasurable X P) (hA : MeasurableSet[m] A) (hAn : NullMeasurableSet A P)
    (f : ℝ →ᵇ ℝ) :
    (∫ ω in A, f (X ω) ∂P) = P.real A * ∫ ω, f (X ω) ∂P := by
  calc
    _ = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) * f (X ω) ∂P := by
      rw [← integral_indicator₀ hAn]
      congr with ω
      by_cases hω : ω ∈ A <;> simp [hω]
    _ = _ := by
      simp only [Pi.one_def]
      rw [IndepFun.integral_fun_comp_mul_comp
        (hI.indicator_indepFun 1 hA)
        ((aemeasurable_indicator_const_iff 1).2 hAn) hX
        measurable_id.aestronglyMeasurable f.continuous.measurable.aestronglyMeasurable]
      simp only [id_eq, integral_indicator₀ hAn, integral_const, smul_eq_mul, mul_one,
        measureReal_def, Measure.restrict_apply_univ]

lemma indep_comap_of_ae_tendsto {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : ∀ A, MeasurableSet[m] A → NullMeasurableSet A P)
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hI : ∀ n, Indep m (MeasurableSpace.comap (X n) (borel ℝ)) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y (borel ℝ)) P := by
  apply (Indep_iff_IndepSets _ _ P).2
  apply indepSets_comap_of_bcf (fun A hA => hm A hA) hY
  intro A hA f
  have hall := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    (hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  have hres := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable.restrict)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    ((ae_restrict_of_ae hlim).mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  apply tendsto_nhds_unique hres
  convert hall.const_mul (P.real A) using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact indep_setIntegral_eq_mul_null P (hI n) (hX n) hA (hm A hA) f

lemma brownian_increment_indep_usual (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval r ω -
        brownianEval ⟨t.val, t.property.1⟩ ω) (borel ℝ)) P := by
  let t₀ : ℝ≥0 := ⟨t.val, t.property.1⟩
  have ht₀r : t₀ < r := htr
  obtain ⟨s, -, hs, hlim⟩ := exists_seq_strictAnti_tendsto' ht₀r
  apply indep_comap_of_ae_tendsto P (fun A hA =>
    (usualBrownianSigma_le_completion P t A hA))
    (X := fun n ω => brownianEval r ω - brownianEval (s n) ω)
    (fun n => ((brownianEval_measurable r).sub (brownianEval_measurable (s n))).aemeasurable)
    (((brownianEval_measurable r).sub (brownianEval_measurable t₀)).aemeasurable)
  · intro n
    have hI := brownian_future_indep_usual_earlier P hB t (s n) (r-s n) (hs n).1
    rwa [add_tsub_cancel_of_le (hs n).2.le] at hI
  · exact Filter.Eventually.of_forall fun ω => tendsto_const_nhds.sub
      (ω.continuous.continuousAt.tendsto.comp hlim)

lemma progressive_clipControl (P : Measure BrownianPath) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) (L : ℝ) : Progressive P (clipControl L v) := by
  intro t
  exact measurable_const.max (measurable_const.min (hv t))

lemma abs_clip_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : |max (-L) (min L x)| ≤ L := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clip_cost_gain {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    L * |x - max (-L) (min L x)| ≤ (x^2 - (max (-L) (min L x))^2)/2 := by
  by_cases hx : x ≤ -L
  · have hxL : x ≤ L := hx.trans (by linarith)
    rw [min_eq_right hxL, max_eq_left hx, abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (x+L)]
  · by_cases hLx : L ≤ x
    · rw [min_eq_left hLx, max_eq_right (by linarith : -L ≤ L),
        abs_of_nonneg (by linarith : 0 ≤ x-L)]
      nlinarith [sq_nonneg (x-L)]
    · rw [min_eq_right (le_of_not_ge hLx), max_eq_right (le_of_not_ge hx)]
      simp

lemma clip_sq_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    (max (-L) (min L x))^2 ≤ x^2 := by
  have h := clip_cost_gain hL x
  nlinarith [mul_nonneg hL (abs_nonneg (x - max (-L) (min L x)))]

lemma pathControlCost_clip_le (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    pathControlCost m (clipControl L v) ω ≤ pathControlCost m v ω := by
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (clip_sq_le hL _) (m.nonneg t))

lemma controlCost_clip_le (P : Measure BrownianPath) (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) : controlCost P m (clipControl L v) ≤ controlCost P m v :=
  lintegral_mono fun ω => pathControlCost_clip_le m hL v ω

lemma weightedTime_integrable (m : Trial) {v : Time → ℝ} (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    Integrable (fun t => m t * v t ^ 2) timeLaw ∧
      Integrable (fun t => m t * v t) timeLaw := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  refine ⟨hq, (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  change |m t * v t| ≤ m t * v t ^ 2 + m t
  rw [abs_mul, abs_of_nonneg (m.nonneg t)]
  have h : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_nonneg (|v t| - 1), sq_abs (v t)]
  nlinarith [mul_le_mul_of_nonneg_left h (m.nonneg t)]

lemma integral_pathControlCost (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, (pathControlCost m v ω).toReal ∂P) = (controlCost P m v).toReal :=
  integral_toReal (pathControlCost_aemeasurable P m hv)
    (ae_lt_top' (pathControlCost_aemeasurable P m hv) hc.ne)

lemma clipping_drift_gain (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    {v : Time → BrownianPath → ℝ} (ω : BrownianPath)
    (hv : Measurable (fun t => v t ω)) (hc : pathControlCost m v ω < ∞) :
    L * |controlDrift m v ω - controlDrift m (clipControl L v) ω| ≤
      ((pathControlCost m v ω).toReal - (pathControlCost m (clipControl L v) ω).toReal)/2 := by
  have hw : Measurable (fun t => clipControl L v t ω) := measurable_const.max (measurable_const.min hv)
  have hcv := weightedTime_integrable m hv hc
  have hcw := weightedTime_integrable m hw ((pathControlCost_clip_le m hL v ω).trans_lt hc)
  have hev : (∫ t, m t * v t ω ^ 2 ∂timeLaw) = (pathControlCost m v ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcv.1.aestronglyMeasurable
  have hew : (∫ t, m t * clipControl L v t ω ^ 2 ∂timeLaw) =
      (pathControlCost m (clipControl L v) ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcw.1.aestronglyMeasurable
  unfold controlDrift
  rw [← integral_sub hcv.2 hcw.2]
  calc
    _ ≤ L * ∫ t, |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hL
    _ = ∫ t, L * |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ t, (m t * v t ω ^ 2 - m t * clipControl L v t ω ^ 2)/2 ∂timeLaw := by
      apply integral_mono ((hcv.2.sub hcw.2).abs.const_mul L) ((hcv.1.sub hcw.1).div_const 2)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg (m.nonneg t)]
      have h := mul_le_mul_of_nonneg_left (clip_cost_gain hL (v t ω)) (m.nonneg t)
      dsimp [clipControl]
      nlinarith
    _ = _ := by rw [integral_div, integral_sub hcv.1 hcw.1, hev, hew]

lemma controlPayoff_le_clipControl (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    controlPayoff P f m v ≤ controlPayoff P f m (clipControl L v) := by
  let w := clipControl L v
  have hw : Progressive P w := progressive_clipControl P hv L
  have hcw : controlCost P m w < ∞ := (controlCost_clip_le P m L.coe_nonneg v).trans_lt hc
  have hpv := pathControlCost_aemeasurable P m hv
  have hpw := pathControlCost_aemeasurable P m hw
  have hcvI := integrable_toReal_of_lintegral_ne_top hpv hc.ne
  have hcwI := integrable_toReal_of_lintegral_ne_top hpw hcw.ne
  have hineq : (∫ ω, (f (brownianEval 1 ω + controlDrift m v ω) -
        f (brownianEval 1 ω + controlDrift m w ω)) ∂P) ≤
      (∫ ω, ((pathControlCost m v ω).toReal - (pathControlCost m w ω).toReal)/2 ∂P) := by
    apply integral_mono_ae ((controlReward_integrable P f m hv).sub (controlReward_integrable P f m hw))
      ((hcvI.sub hcwI).div_const 2)
    filter_upwards [ae_lt_top' hpv hc.ne] with ω hω
    have hLip := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
      (brownianEval 1 ω + controlDrift m w ω)
    rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hLip
    exact (le_abs_self _).trans (hLip.trans
      (clipping_drift_gain m L.coe_nonneg ω (progressive_time_measurable P hv ω) hω))
  rw [integral_sub (controlReward_integrable P f m hv) (controlReward_integrable P f m hw),
    integral_div, integral_sub hcvI hcwI, integral_pathControlCost P m hv hc,
    integral_pathControlCost P m hw hcw] at hineq
  unfold controlPayoff
  change _ ≤ _
  dsimp only [controlDrift, w] at hineq
  linarith

lemma controlValue_le_of_bounded_controls (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) (b : ℝ)
    (hb : ∀ v : Time → BrownianPath → ℝ, Progressive P v → controlCost P m v < ∞ →
      (∀ t ω, |v t ω| ≤ L) → controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  exact (controlPayoff_le_clipControl P f m L hf hv hc).trans
    (hb (clipControl L v) (progressive_clipControl P hv L)
      ((controlCost_clip_le P m L.coe_nonneg v).trans_lt hc)
      (fun t ω => abs_clip_le L.coe_nonneg (v t ω)))

lemma pathControlCost_le_bound (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    pathControlCost m v ω ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _t : Time, ENNReal.ofReal ((L : ℝ)^2) ∂timeLaw := by
      apply lintegral_mono
      intro t
      apply ENNReal.ofReal_le_ofReal
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      exact (mul_le_mul_of_nonneg_right (m.le_one t) (sq_nonneg _)).trans (by simpa using hx)
    _ = _ := by simp

lemma controlCost_le_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) :
    controlCost P m v ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _ω : BrownianPath, ENNReal.ofReal ((L : ℝ)^2) ∂P :=
      lintegral_mono fun ω => pathControlCost_le_bound m L hv ω
    _ = _ := by simp

lemma trial_abs_sub_integrable (m n : Trial) :
    Integrable (fun t => |m t - n t|) timeLaw := by
  apply (integrable_const (2 : ℝ)).mono'
    ((m.measurable.sub n.measurable).abs.aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (m.nonneg t), abs_of_nonneg (n.nonneg t)]; linarith [m.le_one t,n.le_one t])

lemma bounded_drift_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |controlDrift m v ω - controlDrift n v ω| ≤ (L : ℝ) * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  rw [controlDrift, controlDrift, ← integral_sub hm.2 hn.2]
  calc
    _ ≤ ∫ t, |m t * v t ω - n t * v t ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ) * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.2.sub hn.2).abs ((trial_abs_sub_integrable m n).const_mul L)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv t ω) (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma bounded_pathCost_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ≤
      (L : ℝ)^2 * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  have hem : (pathControlCost m v ω).toReal = ∫ t, m t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hm.1.aestronglyMeasurable).symm
  have hen : (pathControlCost n v ω).toReal = ∫ t, n t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (n.nonneg t) (sq_nonneg _))
      hn.1.aestronglyMeasurable).symm
  rw [hem, hen, ← integral_sub hm.1 hn.1]
  calc
    _ ≤ ∫ t, |m t * v t ω ^ 2 - n t * v t ω ^ 2| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ)^2 * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.1.sub hn.1).abs ((trial_abs_sub_integrable m n).const_mul ((L : ℝ)^2))
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (v t ω))]
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma controlPayoff_trial_diff_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hbound : ∀ t ω, |v t ω| ≤ L) :
    |controlPayoff P f m v - controlPayoff P f n v| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  let D := ∫ t, |m t-n t| ∂timeLaw
  have hcm : controlCost P m v < ∞ := (controlCost_le_bound P m L hbound).trans_lt (by finiteness)
  have hcn : controlCost P n v < ∞ := (controlCost_le_bound P n L hbound).trans_lt (by finiteness)
  have hm := controlReward_integrable P f m hv
  have hn := controlReward_integrable P f n hv
  have hrew : |(∫ ω, f (brownianEval 1 ω + controlDrift m v ω) ∂P) -
      (∫ ω, f (brownianEval 1 ω + controlDrift n v ω) ∂P)| ≤ (L : ℝ)^2 * D := by
    rw [← integral_sub hm hn]
    calc
      _ ≤ ∫ ω, |f (brownianEval 1 ω + controlDrift m v ω) -
          f (brownianEval 1 ω + controlDrift n v ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono (hm.sub hn).abs (integrable_const _)
        intro ω
        have hh := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
          (brownianEval 1 ω + controlDrift n v ω)
        rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hh
        have hb := mul_le_mul_of_nonneg_left
          (bounded_drift_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)) L.coe_nonneg
        exact hh.trans (by dsimp only [D]; nlinarith [hb])
      _ = _ := by simp
  have hcost : |(controlCost P m v).toReal - (controlCost P n v).toReal| ≤ (L : ℝ)^2 * D := by
    rw [← integral_pathControlCost P m hv hcm, ← integral_pathControlCost P n hv hcn,
      ← integral_sub (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne)
        (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)]
    calc
      _ ≤ ∫ ω, |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono
          ((integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne).sub
            (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)).abs
          (integrable_const _)
        intro ω
        exact bounded_pathCost_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)
      _ = _ := by simp
  apply abs_le.mpr
  obtain ⟨hrewlo,hrewhi⟩ := abs_le.mp hrew
  obtain ⟨hcostlo,hcosthi⟩ := abs_le.mp hcost
  dsimp only [controlPayoff, controlDrift] at *
  constructor <;> linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianAverage
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma controlValue_trial_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    controlValue P f m - controlValue P f n ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  suffices controlValue P f m ≤ controlValue P f n +
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw by linarith
  apply controlValue_le_of_bounded_controls P f m L hf
  intro v hv _ hbound
  have hpay : controlPayoff P f n v ≤ controlValue P f n :=
    le_csSup (controlPayoffs_bddAbove P f n) ⟨v, hv,
      (controlCost_le_bound P n L hbound).trans_lt (by finiteness), rfl⟩
  have hd := (abs_le.mp (controlPayoff_trial_diff_bound P f m n L hf hv hbound)).2
  linarith

lemma controlValue_trial_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    |controlValue P f m - controlValue P f n| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  have hmn := controlValue_trial_sub_le P f m n L hf
  have hnm := controlValue_trial_sub_le P f n m L hf
  simp_rw [abs_sub_comm (n _) (m _)] at hnm
  exact abs_le.mpr ⟨by linarith, hmn⟩

lemma usual_measurable_aemeasurable (P : Measure BrownianPath) (t : Time)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    AEMeasurable Y P := by
  have h : NullMeasurable Y P := hY.mono (usualBrownianSigma_le_completion P t) le_rfl
  exact h.aemeasurable

lemma brownian_increment_indep_adapted (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    IndepFun Y (fun ω => brownianEval r ω - brownianEval ⟨t.val, (show 0 ≤ (t : ℝ) from t.property.1)⟩ ω) P :=
  indep_of_indep_of_le_left (brownian_increment_indep_usual P hB t r htr) hY.comap_le

lemma second_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2| ≤
      C * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd₁ : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hd₂ : iteratedDerivWithin 2 f (uIcc x y) x = iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc
  have hp : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + iteratedDeriv 2 f x * (y-x)^2/2 := by
    rw [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval, hd₁, hd₂]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2 =
      iteratedDeriv 3 f z * (y-x)^3/6 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (by positivity)) (by norm_num)

lemma first_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x)| ≤ C * (y-x)^2 / 2 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hp : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) = iteratedDeriv 2 f z * (y-x)^2/2 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x))]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (sq_nonneg _)) (by norm_num)

lemma smooth_deriv_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) : LipschitzWith C (deriv f) := by
  apply lipschitzWith_of_nnnorm_deriv_le hf.differentiable_deriv_two
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, coe_nnnorm, Real.norm_eq_abs] using hC x

lemma drift_shift_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x z a : ℝ) :
    |f (x+z+a) - f (x+z) - deriv f x * a| ≤ (C : ℝ) * (|z| * |a| + a^2/2) := by
  have ht := first_order_taylor_bound hf C hC (x+z) (x+z+a)
  simp only [add_sub_cancel_left] at ht
  have hd := (smooth_deriv_lipschitz hf C hC).dist_le_mul (x+z) x
  simp only [Real.dist_eq, add_sub_cancel_left] at hd
  calc
    _ = |(f (x+z+a) - f (x+z) - deriv f (x+z) * a) + (deriv f (x+z) - deriv f x) * a| := by congr 1; ring
    _ ≤ |f (x+z+a) - f (x+z) - deriv f (x+z) * a| + |(deriv f (x+z) - deriv f x) * a| := abs_add_le _ _
    _ ≤ (C : ℝ) * a^2/2 + (C : ℝ) * |z| * |a| := by
      rw [abs_mul]
      exact add_le_add ht (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    _ = _ := by ring

lemma gaussian_abs_moment (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
      (Real.sqrt v)^n * ∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt v)^2, sq_nonneg _⟩ : ℝ≥0) = v := by
    ext; exact Real.sq_sqrt v.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  simp only [mul_zero, NNReal.mk] at hL
  rw [hv, mul_one] at hL
  rw [← hL.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^n) (gaussianReal 0 v))]
  simp only [Function.comp_apply, id_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

lemma gaussian_law_integrable_abs_pow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) (n : ℕ) :
    Integrable (fun ω => |Z ω|^n) P := by
  have hm : MemLp id (n : ℝ≥0∞) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) (n : ℝ≥0))
  have hi : Integrable (fun x : ℝ => |x|^n) (Measure.map Z P) := by
    rw [hZ.map_eq]
    simpa only [Real.norm_eq_abs, id_eq] using hm.integrable_norm_pow'
  exact (integrable_map_measure hi.aestronglyMeasurable hZ.aemeasurable).mp hi

lemma gaussian_law_sq_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) :
    (∫ ω, (Z ω)^2 ∂P) = v := by
  have hi := hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2)
    (gaussianReal 0 v))
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  simp only [variance_id_gaussianReal, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    zero_pow (by decide : 2 ≠ 0), sub_zero] at hv
  exact hi.trans hv.symm

lemma gaussian_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₂ C₃ : ℝ) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) :
    |(∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  let d₁ := deriv (f : ℝ → ℝ)
  let d₂ := iteratedDeriv 2 (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hm₂ : Measurable d₂ := (hf.continuous_iteratedDeriv 2 (by norm_num)).measurable
  have hi₁ : Integrable (fun ω => d₁ (X ω) * Z ω) P := by
    have hz : Integrable Z P := by
      have hi := gaussian_law_integrable_abs_pow hZ 1
      exact (integrable_norm_iff hZ.aemeasurable.aestronglyMeasurable).mp (by
        simpa only [pow_one, Real.norm_eq_abs] using hi)
    apply hz.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have hi₂ : Integrable (fun ω => d₂ (X ω) * (Z ω)^2) P := by
    have hz : Integrable (fun ω => (Z ω)^2) P := by
      simpa only [sq_abs] using gaussian_law_integrable_abs_pow hZ 2
    apply hz.bdd_mul (hm₂.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₂] using h₂ (X ω)
  have hv₁ : (∫ ω, d₁ (X ω) * Z ω ∂P) = 0 := by
    have hh := (hI.comp hm₁ measurable_id).integral_fun_mul_eq_mul_integral
      (hm₁.comp_aemeasurable hX).aestronglyMeasurable hZ.aemeasurable.aestronglyMeasurable
    have hz : (∫ ω, Z ω ∂P) = 0 := hZ.integral_eq.trans (integral_id_gaussianReal)
    simpa only [Function.comp_apply, id_eq, hz, mul_zero] using hh
  have hv₂ : (∫ ω, d₂ (X ω) * (Z ω)^2 ∂P) = (v : ℝ) * (∫ ω, d₂ (X ω) ∂P) := by
    have hh := (hI.comp hm₂ (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      (hm₂.comp_aemeasurable hX).aestronglyMeasurable (hZ.aemeasurable.pow_const 2).aestronglyMeasurable
    simp only [Function.comp_apply, id_eq] at hh
    exact hh.trans (by rw [gaussian_law_sq_mean hZ, mul_comm])
  let R := fun ω => f (X ω + Z ω) - f (X ω) - d₁ (X ω) * Z ω - d₂ (X ω) * (Z ω)^2/2
  have hiR : Integrable R P :=
    (((boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)).sub
      (boundedContinuousFunction_integrable_comp f hX)).sub hi₁).sub (hi₂.div_const 2)
  have hR : ∀ ω, |R ω| ≤ C₃/6 * |Z ω|^3 := by
    intro ω
    have hh := second_order_taylor_bound hf C₃ h₃ (X ω) (X ω + Z ω)
    simpa only [add_sub_cancel_left, R, d₁, d₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hbound : |∫ ω, R ω ∂P| ≤ C₃/6 * ∫ ω, |Z ω|^3 ∂P := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C₃/6 * |Z ω|^3 ∂P := integral_mono hiR.abs
        ((gaussian_law_integrable_abs_pow hZ 3).const_mul _) hR
      _ = _ := integral_const_mul _ _
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, d₂ (X ω) ∂P := by
    have ha := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
    have hb := boundedContinuousFunction_integrable_comp f hX
    have he₁ := integral_sub ((ha.sub hb).sub hi₁) (hi₂.div_const 2)
    have he₂ := integral_sub (ha.sub hb) hi₁
    have he₃ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂ he₃
    dsimp only [R]
    rw [he₁, he₂, he₃, integral_div, hv₁, hv₂]
    ring
  have hg : (∫ ω, |Z ω|^3 ∂P) = (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 :=
    (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^3) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 3)
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma drift_shift_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (C₁ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P)| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) := by
  let d₁ := deriv (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hiA := bounded_real_integrable hA K (Filter.Eventually.of_forall hAK)
  have hi₁ : Integrable (fun ω => d₁ (X ω) * A ω) P := by
    apply hiA.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have ha := boundedContinuousFunction_integrable_comp f ((hX.add hZ.aemeasurable).add hA)
  have hb := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
  let R := fun ω => f (X ω + Z ω + A ω) - f (X ω + Z ω) - d₁ (X ω) * A ω
  have hiR : Integrable R P := (ha.sub hb).sub hi₁
  have hR : ∀ ω, |R ω| ≤ (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) := by
    intro ω
    apply (drift_shift_taylor_bound hf C₂ h₂ (X ω) (Z ω) (A ω)).trans
    apply mul_le_mul_of_nonneg_left _ C₂.coe_nonneg
    have hsq : A ω ^2 ≤ (K : ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (A ω)) K.coe_nonneg).mpr (hAK ω)
    exact add_le_add (mul_le_mul_of_nonneg_left (hAK ω) (abs_nonneg _)) (by linarith)
  have hiz : Integrable (fun ω => |Z ω|) P := by
    simpa only [pow_one] using gaussian_law_integrable_abs_pow hZ 1
  have hbound : |∫ ω, R ω ∂P| ≤
      (C₂ : ℝ) * ((∫ ω, |Z ω| ∂P) * (K : ℝ) + (K : ℝ)^2/2) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) ∂P :=
        integral_mono hiR.abs (((hiz.mul_const K).add (integrable_const _)).const_mul C₂) hR
      _ = _ := by rw [integral_const_mul, integral_add (hiz.mul_const K) (integrable_const _), integral_mul_const]; simp
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω + A ω) ∂P) -
      (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, d₁ (X ω) * A ω ∂P) := by
    have he₁ := integral_sub (ha.sub hb) hi₁
    have he₂ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂
    exact he₁.trans (by rw [he₂])
  have hg : (∫ ω, |Z ω| ∂P) = Real.sqrt v * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
    have hh := (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^1) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 1)
    simpa only [pow_one, Function.comp_apply] using hh
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma gaussian_drift_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₃ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) +
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  have hG := gaussian_taylor_mean_bound f hf C₁ C₂ C₃ h₁ h₂ h₃ hX hZ hI
  have hD := drift_shift_mean_bound f (hf.of_le (by norm_num)) C₁ C₂ K h₁ h₂ hX hZ hA hAK
  have hh := abs_add_le
    ((∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P))
    ((∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P)
  convert hh.trans (add_le_add hD hG) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma gaussianAverage_semigroup (s t : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (gaussianAverageBCF t f) x = gaussianAverage (s+t) f x := by
  have hi : Integrable (fun z => f (x+z)) ((gaussianReal 0 s) ∗ (gaussianReal 0 t)) := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
    exact gaussianAverage_integrable (s+t) f x
  have hh := integral_conv hi
  simp only [gaussianReal_conv_gaussianReal, zero_add] at hh
  simpa only [gaussianAverage, gaussianAverageBCF_coe, add_assoc] using hh.symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatLogBCF
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

lemma exp_heatLog (s d : ℝ≥0) (hd : d ≠ 0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (d * heatLog s d f x) = gaussianAverage s (expBCF d f) x := by
  simp only [heatLog, hd, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hd), one_mul,
    Real.exp_log (gaussianAverage_exp_pos s d f x)]

lemma heatLog_zero (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : heatLog 0 d f x = f x := by
  by_cases hd : d = 0
  · simp [heatLog, hd]
  · simp [heatLog, hd]

lemma heatLog_semigroup (s t d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    heatLog s d (heatLogBCF t d f) x = heatLog (s+t) d f x := by
  by_cases hd : d = 0
  · subst d
    have he : heatLogBCF t 0 f = gaussianAverageBCF t f := by ext z; simp [heatLog]
    simp only [heatLog, ↓reduceIte, he]
    exact gaussianAverage_semigroup s t f x
  · have he : expBCF d (heatLogBCF t d f) = gaussianAverageBCF t (expBCF d f) := by
      ext z
      exact exp_heatLog t d hd f z
    simp only [heatLog, hd, ↓reduceIte, he, gaussianAverage_semigroup]

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv
lemma Jet3.deriv2_eq (g : Jet3) : iteratedDeriv 2 (g.f : ℝ → ℝ) = g.d2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, g.deriv_eq]
  exact funext fun x => (g.has2 x).deriv
lemma Jet3.deriv3_eq (g : Jet3) : iteratedDeriv 3 (g.f : ℝ → ℝ) = g.d3 := by
  rw [iteratedDeriv_succ, g.deriv2_eq]
  exact funext fun x => (g.has3 x).deriv

lemma Jet3.contDiff (g : Jet3) : ContDiff ℝ 3 (g.f : ℝ → ℝ) := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has1 x).differentiableAt, by norm_num, ?_⟩
  rw [g.deriv_eq, show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has2 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d1 : ℝ → ℝ) = g.d2 from funext fun x => (g.has2 x).deriv,
    show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has3 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d2 : ℝ → ℝ) = g.d3 from funext fun x => (g.has3 x).deriv]
  exact contDiff_zero.mpr g.d3.continuous

lemma Jet3.gaussianAverage_norms (s : ℝ≥0) (g : Jet3) :
    ‖(g.gaussianAverage s).f‖ ≤ ‖g.f‖ ∧ ‖(g.gaussianAverage s).d1‖ ≤ ‖g.d1‖ ∧
    ‖(g.gaussianAverage s).d2‖ ≤ ‖g.d2‖ ∧ ‖(g.gaussianAverage s).d3‖ ≤ ‖g.d3‖ := by
  have hh (f : ℝ →ᵇ ℝ) : ‖gaussianAverageBCF s f‖ ≤ ‖f‖ := by
    rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
    intro x; exact gaussianAverage_abs_le s f x
  exact ⟨hh _,hh _,hh _,hh _⟩

lemma invBCF_norm_le (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) :
    ‖invBCF g c hc hg‖ ≤ c⁻¹ := by
  rw [BoundedContinuousFunction.norm_le (inv_nonneg.mpr hc.le)]
  intro x; exact inv_bcf_bound hc hg x

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptronFreeEnergy.heatLog]
  · rfl

lemma gaussianAverage_jet_error (s : ℝ≥0) (g : Jet3) (x : ℝ) :
    |gaussianAverage s g.f x - g.f x - (s : ℝ)/2 * g.d2 x| ≤
      ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by
  have hh := gaussian_taylor_mean_bound (P := gaussianReal 0 s) g.f g.contDiff
    ‖g.d1‖ ‖g.d2‖ ‖g.d3‖
    (fun y => by rw [g.deriv_eq]; exact g.d1.norm_coe_le_norm y)
    (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y)
    (fun y => by rw [g.deriv3_eq]; exact g.d3.norm_coe_le_norm y)
    (X := fun _ : ℝ => x) aemeasurable_const (Z := id) HasLaw.id (indepFun_const_left _ _)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, g.deriv2_eq, gaussianAverage, id_eq] using hh

lemma log_linear_error_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b - Real.log a - (b-a)/a| ≤ (b-a)^2 / c^2 := by
  have ha0 := hc.trans_le ha
  have hb0 := hc.trans_le hb
  have hu := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hu
  rw [Real.log_div ha0.ne' hb0.ne'] at hl
  have heq : b/a-1 = (b-a)/a := by field_simp
  rw [heq] at hu
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  have hlin : -(Real.log b - Real.log a - (b-a)/a) ≤ (b-a)^2/(a*b) := by
    have he : (b-a)/a + (a/b-1) = (b-a)^2/(a*b) := by field_simp; ring
    linarith
  exact hlin.trans (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hc)
    (by nlinarith [mul_le_mul ha hb hc.le ha0.le]))

lemma gaussianAverage_ge_const (s : ℝ≥0) (f : ℝ →ᵇ ℝ) {c : ℝ}
    (hc : ∀ x, c ≤ f x) (x : ℝ) : c ≤ gaussianAverage s f x := by
  have hh := integral_mono (integrable_const c) (gaussianAverage_integrable s f x) (fun z => hc (x+z))
  simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma log_gaussian_generator_error (g : Jet3) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x, c ≤ g.f x) (C₂ C₃ : ℝ≥0) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃)
    (s : ℝ≥0) (hs : s ≤ 1) (x : ℝ) :
    |Real.log (gaussianAverage s g.f x) - Real.log (g.f x) -
      (s : ℝ)/2 * g.d2 x / g.f x| ≤
      (((C₂ : ℝ)/2 + (C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))^2/c^2 +
        ((C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))/c) * (s : ℝ) * Real.sqrt s := by
  let A := gaussianAverage s g.f x
  let a := g.f x
  let K := (C₃ : ℝ)/6 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  let D := (C₂ : ℝ)/2 + K
  have ha := hg x
  have hA := gaussianAverage_ge_const s g.f hg x
  have hM : 0 ≤ ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := integral_nonneg (fun z => by positivity)
  have hK : 0 ≤ K := by positivity
  have hD : 0 ≤ D := by positivity
  have hs0 : 0 ≤ (s : ℝ) := s.coe_nonneg
  have hs1 : (s : ℝ) ≤ 1 := hs
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := (Real.sqrt_le_one).mpr hs1
  have hrsq := Real.sq_sqrt hs0
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ) * Real.sqrt (s : ℝ) := by nlinarith
  have herr : |A-a-(s : ℝ)/2*g.d2 x| ≤ K * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by gcongr
      _ = _ := by rw [hrcube]; unfold K; ring
  have hdx : |g.d2 x| ≤ C₂ := (g.d2.norm_coe_le_norm x).trans h₂
  have hdelta : |A-a| ≤ D * (s : ℝ) := by
    have habs := abs_add_le (A-a-(s : ℝ)/2*g.d2 x) ((s : ℝ)/2*g.d2 x)
    rw [sub_add_cancel] at habs
    have hterm : |(s : ℝ)/2*g.d2 x| ≤ (s : ℝ)/2*C₂ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s/2)]
      exact mul_le_mul_of_nonneg_left hdx (by positivity)
    have hkr := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hK hs0)
    dsimp [D]; nlinarith
  have hquad : (A-a)^2/c^2 ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s := by
    have hdsq : (A-a)^2 ≤ (D*(s : ℝ))^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (A-a)) (mul_nonneg hD hs0)).mpr hdelta
      simpa only [sq_abs] using hh
    calc
      _ ≤ (D*(s : ℝ))^2/c^2 := div_le_div_of_nonneg_right hdsq (sq_nonneg c)
      _ = D^2/c^2 * (s : ℝ)^2 := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsr hs0)
          (show 0 ≤ D^2/c^2 by positivity)
        nlinarith only [hh]
  have hrem : |A-a-(s : ℝ)/2*g.d2 x|/a ≤ (K/c) * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ (K*(s : ℝ)*Real.sqrt s)/c := div_le_div₀ (by positivity) herr hc ha
      _ = _ := by ring
  have hlog := log_linear_error_le hc ha hA
  change |Real.log A - Real.log a - (s : ℝ)/2*g.d2 x/a| ≤ _
  calc
    _ = |(Real.log A-Real.log a-(A-a)/a) + (A-a-(s : ℝ)/2*g.d2 x)/a| := by congr 1; ring
    _ ≤ |Real.log A-Real.log a-(A-a)/a| + |(A-a-(s : ℝ)/2*g.d2 x)/a| := abs_add_le _ _
    _ = |Real.log A-Real.log a-(A-a)/a| + |A-a-(s : ℝ)/2*g.d2 x|/a := by
      rw [abs_div, abs_of_pos (hc.trans_le ha)]
    _ ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s + (K/c)*(s : ℝ)*Real.sqrt s :=
      add_le_add (hlog.trans hquad) hrem
    _ = _ := by dsimp [D,K]; ring

lemma expBCF_norm_le (d : ℝ) (f : ℝ →ᵇ ℝ) :
    ‖expBCF d f‖ ≤ Real.exp (|d| * ‖f‖) := by
  rw [BoundedContinuousFunction.norm_le (Real.exp_pos _).le]
  exact exp_bcf_bound d f

lemma Jet3.exp_norms (g : Jet3) (d C₀ C₁ C₂ C₃ : ℝ≥0)
    (h₀ : ‖g.f‖ ≤ C₀) (h₁ : ‖g.d1‖ ≤ C₁) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃) :
    let E := Real.exp ((d : ℝ)*C₀)
    ‖(g.exp d).f‖ ≤ E ∧ ‖(g.exp d).d1‖ ≤ (d : ℝ)*E*C₁ ∧
    ‖(g.exp d).d2‖ ≤ E*((d : ℝ)^2*C₁^2 + d*C₂) ∧
    ‖(g.exp d).d3‖ ≤ E*((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*C₁*C₂ + d*C₃) := by
  dsimp only
  have hf : ‖expBCF d g.f‖ ≤ Real.exp ((d : ℝ)*C₀) := by
    refine (expBCF_norm_le d g.f).trans ?_
    rw [abs_of_nonneg d.coe_nonneg]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h₀ d.coe_nonneg)
  refine ⟨hf, ?_, ?_, ?_⟩
  · change ‖(d : ℝ) • (expBCF d g.f * g.d1)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ) * (‖expBCF d g.f‖ * ‖g.d1‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ (d : ℝ) * (Real.exp ((d : ℝ)*C₀) * C₁) := by gcongr
      _ = _ := by ring
  · change ‖expBCF d g.f * ((d : ℝ)^2 • (g.d1^2) + (d : ℝ) • g.d2)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * (‖(d : ℝ)^2 • (g.d1^2)‖ + ‖(d : ℝ) • g.d2‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^2 * ‖g.d1^2‖ + (d : ℝ) * ‖g.d2‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg, abs_pow]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^2 * C₁^2 + (d : ℝ) * C₂) := by
        gcongr
        exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖expBCF d g.f * ((d : ℝ)^3 • (g.d1^3) + (3*(d : ℝ)^2) • (g.d1*g.d2) + (d : ℝ) • g.d3)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * ((‖(d : ℝ)^3 • (g.d1^3)‖ + ‖(3*(d : ℝ)^2) • (g.d1*g.d2)‖) + ‖(d : ℝ) • g.d3‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^3 * ‖g.d1^3‖ + 3*(d : ℝ)^2*‖g.d1*g.d2‖ + (d : ℝ)*‖g.d3‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)^3),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3*(d : ℝ)^2), abs_of_nonneg d.coe_nonneg]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*(C₁*C₂) + (d : ℝ)*C₃) := by
        gcongr
        · exact (norm_pow_le _ _).trans (by gcongr)
        · exact (norm_mul_le _ _).trans (by gcongr)
      _ = _ := by ring

lemma Jet3.heatLog_uniform_bounds (d : ℝ≥0) (g : Jet3) :
    ∃ C₀ C₁ C₂ C₃ : ℝ≥0, ∀ s : ℝ≥0,
      ‖(g.heatLog s d).f‖ ≤ C₀ ∧ ‖(g.heatLog s d).d1‖ ≤ C₁ ∧
      ‖(g.heatLog s d).d2‖ ≤ C₂ ∧ ‖(g.heatLog s d).d3‖ ≤ C₃ := by
  by_cases hd : d = 0
  · subst d
    refine ⟨‖g.f‖₊, ‖g.d1‖₊, ‖g.d2‖₊, ‖g.d3‖₊, ?_⟩
    intro s; simpa only [Jet3.heatLog, ↓reduceDIte, coe_nnnorm] using g.gaussianAverage_norms s
  let e := g.exp d
  let B := (Real.exp (-(d : ℝ)*‖g.f‖))⁻¹
  let r := (d : ℝ)⁻¹
  have hB : 0 ≤ B := by positivity
  have hr : 0 ≤ r := by positivity
  refine ⟨‖g.f‖₊,
    ⟨r*(‖e.d1‖*B), by positivity⟩,
    ⟨r*(‖e.d2‖*B+‖e.d1‖^2*B^2), by positivity⟩,
    ⟨r*(‖e.d3‖*B+3*(‖e.d1‖*‖e.d2‖*B^2)+2*(‖e.d1‖^3*B^3)), by positivity⟩, ?_⟩
  intro s
  let A := e.gaussianAverage s
  let c := Real.exp (-(d : ℝ)*‖g.f‖)
  let hc := Real.exp_pos (-(d : ℝ)*‖g.f‖)
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  have hj : ‖J‖ ≤ B := invBCF_norm_le A.f c hc hA
  obtain ⟨_, h₁,h₂,h₃⟩ := e.gaussianAverage_norms s
  have hf : ‖(g.heatLog s d).f‖ ≤ ‖g.f‖ := by
    rw [g.heatLog_f, BoundedContinuousFunction.norm_le (norm_nonneg _)]
    exact heatLog_abs_le s d g.f
  rw [Jet3.heatLog, dite_eq_right hd]
  refine ⟨by simpa only [Jet3.heatLog, dite_eq_right hd, coe_nnnorm] using hf, ?_, ?_, ?_⟩
  · change ‖r • (A.d1*J)‖ ≤ r * (‖e.d1‖*B)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (by gcongr)) hr
  · change ‖r • (A.d2*J - A.d1^2*J^2)‖ ≤ r*(‖e.d2‖*B+‖e.d1‖^2*B^2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖r • (A.d3*J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_mul_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)

lemma heatLog_generator_uniform (d C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ →
      ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ → ∀ (s : ℝ≥0), s ≤ 1 → ∀ x : ℝ,
        |heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)| ≤
          (C : ℝ) * (s : ℝ) * Real.sqrt s := by
  let M := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg (fun z => by positivity)
  by_cases hd : d = 0
  · subst d
    refine ⟨⟨(C₃ : ℝ)/6*M, by positivity⟩, ?_⟩
    intro g _ _ _ h₃ s _ x
    simp only [heatLog, ↓reduceIte, NNReal.coe_zero, zero_mul, add_zero]
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * M := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * M := by gcongr
      _ = (C₃ : ℝ)/6*M * (s : ℝ) * Real.sqrt s := by
        have hh := Real.sq_sqrt s.coe_nonneg
        calc
          _ = (C₃ : ℝ)/6*M * (Real.sqrt s)^2 * Real.sqrt s := by ring
          _ = _ := by rw [hh]
  let c := Real.exp (-(d : ℝ)*C₀)
  let E := Real.exp ((d : ℝ)*C₀)
  let E₂ : ℝ≥0 := ⟨E*((d : ℝ)^2*C₁^2+(d : ℝ)*C₂), by positivity⟩
  let E₃ : ℝ≥0 := ⟨E*((d : ℝ)^3*C₁^3+3*(d : ℝ)^2*C₁*C₂+(d : ℝ)*C₃), by positivity⟩
  let K := ((E₂ : ℝ)/2+(E₃ : ℝ)/6*M)^2/c^2 + ((E₃ : ℝ)/6*M)/c
  have hc : 0 < c := Real.exp_pos _
  have hK : 0 ≤ K := by positivity
  have hdpos : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  refine ⟨⟨(d : ℝ)⁻¹*K, by positivity⟩, ?_⟩
  intro g h₀ h₁ h₂ h₃ s hs x
  have hh := g.exp_norms d C₀ C₁ C₂ C₃ h₀ h₁ h₂ h₃
  have hlo (x : ℝ) : c ≤ (g.exp d).f x := by
    change Real.exp (-(d : ℝ)*C₀) ≤ Real.exp ((d : ℝ)*g.f x)
    apply Real.exp_le_exp.mpr
    have hb : |g.f x| ≤ C₀ := (g.f.norm_coe_le_norm x).trans h₀
    nlinarith [(abs_le.mp hb).1]
  have herr := log_gaussian_generator_error (g.exp d) c hc hlo E₂ E₃ hh.2.2.1 hh.2.2.2 s hs x
  have he : (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x =
      (d : ℝ) * ((s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)) := by
    change (s : ℝ)/2 * (Real.exp ((d : ℝ)*g.f x) * ((d : ℝ)^2*g.d1 x^2 + (d : ℝ)*g.d2 x)) /
      Real.exp ((d : ℝ)*g.f x) = _
    field_simp
    ring
  have hid : heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x+(d : ℝ)*g.d1 x^2) =
      (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (g.exp d).f x) - Real.log ((g.exp d).f x) -
        (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x) := by
    rw [he]
    change _ = (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (expBCF d g.f) x) -
      Real.log (Real.exp ((d : ℝ)*g.f x)) - _)
    rw [Real.log_exp]
    simp only [heatLog, hd, ↓reduceIte]
    field_simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hdpos)]
  calc
    _ ≤ (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hdpos.le)
    _ = _ := by change (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) = (d : ℝ)⁻¹*K*(s : ℝ)*Real.sqrt s; ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BcfEvalRingHom
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
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma gaussianAverage_scaling (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s f x = ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt s)^2, sq_nonneg _⟩ : ℝ≥0) = s := by
    ext; exact Real.sq_sqrt s.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt s)
  simp only [mul_zero,NNReal.mk] at hL
  rw [hv,mul_one] at hL
  exact (hL.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun z => f (x+z)) (gaussianReal 0 s))).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma mem_interior_integrableExpSet_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    t ∈ interior (integrableExpSet X μ) := by
  have he : integrableExpSet X μ=univ := Set.eq_univ_of_forall hX
  simp [he]

omit [IsProbabilityMeasure μ] in
lemma cgf_analytic_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    AnalyticAt ℝ (cgf X μ) t :=
  analyticAt_cgf (mem_interior_integrableExpSet_of_all μ hX t)

lemma entropicMean_eq_div (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {p : ℝ} (hp : p ≠ 0) : entropicMean μ p X=cgf X μ p/p := by
  rw [entropicMean,intervalIntegral.integral_comp_mul_left _ hp]
  simp only [mul_zero,mul_one]
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (cgf_analytic_of_all μ hX t).differentiableAt.hasDerivAt)
    (hc.intervalIntegrable _ _),cgf_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma entropicMean_zero (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    entropicMean μ 0 X=∫ ω, X ω ∂μ := by
  simp [entropicMean,deriv_cgf_zero (mem_interior_integrableExpSet_of_all μ hX 0)]

end

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma timeTail_atom_integral (q t : Time) (w : ℝ) :
    (∫ s in Ici t, (if q ≤ s then w else 0) ∂timeLaw) = w*(1-max (q:ℝ) (t:ℝ)) := by
  change (∫ s in Ici t, (Ici q).indicator (fun _ => w) s ∂timeLaw) = _
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  rw [Ici_inter_Ici]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,timeLaw_eq_volume,
    unitInterval.volume_Ici,ENNReal.toReal_ofReal (sub_nonneg.mpr (max q t).2.2),smul_eq_mul]
  rcases le_total q t with h | h
  · rw [max_eq_right h,max_eq_right (show (q:ℝ) ≤ (t:ℝ) from h)]
    ring
  · rw [max_eq_left h,max_eq_left (show (t:ℝ) ≤ (q:ℝ) from h)]
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepDual
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

lemma finite_sum_successive_differences (k : ℕ) (v : Fin (k+1) → ℝ) :
    (∑ i : Fin k, (v i.succ-v i.castSucc)) = v (Fin.last k)-v 0 := by
  have h1 := Fin.sum_univ_succ v
  have h2 := Fin.sum_univ_castSucc v
  rw [Finset.sum_sub_distrib]
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CoupledDual
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma Trial.ext_fun {m n : Trial} (h : ∀ t, m t=n t) : m=n := by
  cases m
  cases n
  congr 1
  exact funext h

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

lemma uniformQuantileGrid_strict (n : ℕ) : StrictMono (uniformQuantileGrid n) := by
  intro i j hij
  change (i:ℝ)/(n+1)<(j:ℝ)/(n+1)
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

lemma uniformQuantileGrid_zero (n : ℕ) : uniformQuantileGrid n 0=0 := by
  apply Subtype.ext
  norm_num [uniformQuantileGrid]

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

lemma uniformQuantileCell_atom {n : ℕ} {u : Time} (hu : (u:ℝ)<1) (i : Fin (n+1)) :
    uniformQuantileCell n u=i ↔
      u∈Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
  rw [Fin.ext_iff,uniformQuantileCell_floor hu]
  rw [Nat.floor_eq_iff (mul_nonneg (by positivity) u.2.1)]
  change ((i:ℝ)≤(n+1:ℝ)*(u:ℝ) ∧ (n+1:ℝ)*(u:ℝ)<(i:ℝ)+1) ↔
    ((i:ℝ)/(n+1)≤(u:ℝ) ∧ (u:ℝ)<((i.val+1:ℕ):ℝ)/(n+1))
  rw [div_le_iff₀ (by positivity),lt_div_iff₀ (by positivity)]
  push_cast
  ring_nf

lemma uniformQuantileCell_weight (n : ℕ) (i : Fin (n+1)) :
    timeLaw.real ((uniformQuantileCell n) ⁻¹' {i})=1/(n+1:ℝ) := by
  have hae : ((uniformQuantileCell n) ⁻¹' {i})=ᵐ[timeLaw]
      Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
    have hnot : ∀ᵐ u ∂timeLaw, u≠1 := by exact ae_iff.mpr (by simp)
    filter_upwards [hnot] with u hu
    exact propext (uniformQuantileCell_atom (lt_of_le_of_ne u.2.2 (fun he => hu (Subtype.ext he))) i)
  rw [measureReal_congr hae]
  simp only [Measure.real,timeLaw_eq_volume,unitInterval.volume_Ico]
  rw [ENNReal.toReal_ofReal]
  · dsimp [uniformQuantileGrid]
    push_cast
    ring
  · exact sub_nonneg.mpr ((uniformQuantileGrid_strict n).monotone (Fin.castSucc_le_succ i))

lemma uniformQuantileCell_integral (n : ℕ) (F : Fin (n+1)→ℝ) :
    (∫ u, F (uniformQuantileCell n u) ∂timeLaw)=∑ i, (1/(n+1:ℝ))*F i := by
  rw [integral_finite_label _ (uniformQuantileCell_measurable n)]
  simp_rw [uniformQuantileCell_weight]

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

theorem freshReplicaKernel_eq_of_pair_law (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ Q, freshReplicaArrayKernel f r Q ∂(μ : Measure (CompactArray CompactJointOverlap)))=
    ∫ Q, freshReplicaArrayKernel f r Q ∂(ν : Measure (CompactArray CompactJointOverlap)) := by
  cases r with
  | zero =>
    have he : ∀ Q : CompactArray CompactJointOverlap,
        freshReplicaArrayKernel f 0 Q=freshReplicaMatrixKernel f 0 (fun _ _ => 0) := by
      intro Q
      change freshReplicaMatrixKernel f 0 _=_
      congr 1
      exact Subsingleton.elim _ _
    simp only [he,integral_const,probReal_univ,one_smul]
  | succ r =>
    let F := freshReplicaMatrixKernel f (r+1)
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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshGGLogUniqueness
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

lemma probability_Icc_eq_of_moments {a b : ℝ} (μ ν : ProbabilityMeasure (Icc a b))
    (hm : ∀ r : ℕ, (∫ x, x.val^r ∂(μ : Measure (Icc a b)))=
      ∫ x, x.val^r ∂(ν : Measure (Icc a b))) : μ=ν := by
  have h : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro F
    apply integral_continuous_tendsto_of_moments (fun _ : ℕ => (μ : Measure (Icc a b)))
      (ν : Measure (Icc a b)) (fun r => ?_) F.toContinuousMap
    rw [hm r]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds h

variable (μ ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
variable (hGGμ : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
variable (hGGν : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν n i f g=0)
variable (hμ : ∀ᵐ Q ∂(μ : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hν : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hpair : (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
  (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))
variable (f : ℝ →ᵇ ℝ) (η ξ : ProbabilityMeasure (FreshPartitionRange f))
variable (hη : ∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange f)))=
  ∫ Q, freshReplicaArrayKernel (expBCF 1 f) r Q ∂(μ : Measure (CompactArray CompactJointOverlap)))
variable (hξ : ∀ r, (∫ x, x.val^r ∂(ξ : Measure (FreshPartitionRange f)))=
  ∫ Q, freshReplicaArrayKernel (expBCF 1 f) r Q ∂(ν : Measure (CompactArray CompactJointOverlap)))

include hGGμ hGGν hμ hν hpair hη hξ in
theorem freshPartitionLaw_eq_of_pair_law : η=ξ := by
  apply probability_Icc_eq_of_moments
  intro r
  rw [hη r,hξ r]
  exact freshReplicaKernel_eq_of_pair_law μ ν hGGμ hGGν hμ hν hpair (expBCF 1 f) r

include hGGμ hGGν hμ hν hpair hη hξ in
theorem freshLog_eq_of_pair_law :
    (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange f)))=
      ∫ x, Real.log x.val ∂(ξ : Measure (FreshPartitionRange f)) := by
  rw [freshPartitionLaw_eq_of_pair_law μ ν hGGμ hGGν hμ hν hpair f η ξ hη hξ]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compact_moment_limit {a b : ℝ} (μ : ℕ→ProbabilityMeasure (Icc a b))
    (mom : ℕ→ℝ)
    (hmom : ∀ r, Tendsto (fun n => ∫ x, x.val^r ∂(μ n : Measure (Icc a b))) atTop (𝓝 (mom r))) :
    ∃ ν : ProbabilityMeasure (Icc a b), Tendsto μ atTop (𝓝 ν) ∧
      ∀ r, (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
  obtain ⟨ν, -, s, hs, hsub⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  have hm r : (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
    let F : Icc a b→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => x.val^r,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hsub
    have h₂ := (hmom r).comp hs.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨ν,?_,hm⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  apply integral_continuous_tendsto_of_moments (fun n => (μ n : Measure (Icc a b)))
    (ν : Measure (Icc a b)) (fun r => ?_) F.toContinuousMap
  rw [hm]
  exact hmom r


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlledPrefix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma heatLog_control_step_error (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      ∀ (s : ℝ≥0), s ≤ 1 → ∀ (X Z A : Ω → ℝ), AEMeasurable X P →
        HasLaw Z (gaussianReal 0 s) P → IndepFun X Z P → AEMeasurable A P →
        (∀ ω, |A ω| ≤ (L : ℝ)*s) →
        |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, heatLog s d g.f (X ω) ∂P) -
          (∫ ω, g.d1 (X ω)*A ω ∂P) + (d : ℝ)*(s : ℝ)/2 * (∫ ω, (g.d1 (X ω))^2 ∂P)| ≤
          (C : ℝ)*(s : ℝ)*Real.sqrt s := by
  obtain ⟨C,hC⟩ := heatLog_generator_uniform d C₀ C₁ C₂ C₃
  let M₁ := ∫ z : ℝ, |z| ∂gaussianReal 0 1
  let M₃ := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM₁ : 0 ≤ M₁ := integral_nonneg (fun z => abs_nonneg z)
  have hM₃ : 0 ≤ M₃ := integral_nonneg (fun z => by positivity)
  let K := (C₂ : ℝ)*((L : ℝ)*M₁+(L : ℝ)^2/2) + (C₃ : ℝ)/6*M₃
  have hK : 0 ≤ K := by positivity
  refine ⟨⟨K+C, by positivity⟩, ?_⟩
  intro Ω _ P _ g h₀ h₁ h₂ h₃ s hs X Z A hX hZ hI hA hAK
  have hG := gaussian_drift_taylor_mean_bound g.f g.contDiff C₁ C₃ C₂ (L*s)
    (fun y => by rw [g.deriv_eq]; exact (g.d1.norm_coe_le_norm y).trans h₁)
    (fun y => by rw [g.deriv2_eq]; exact (g.d2.norm_coe_le_norm y).trans h₂)
    (fun y => by rw [g.deriv3_eq]; exact (g.d3.norm_coe_le_norm y).trans h₃)
    hX hZ hI hA (by simpa only [NNReal.coe_mul] using hAK)
  rw [g.deriv_eq, g.deriv2_eq] at hG
  have hs0 := s.coe_nonneg
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := Real.sqrt_le_one.mpr hs
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith [Real.sq_sqrt hs0]
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ)*Real.sqrt s := by nlinarith [Real.sq_sqrt hs0]
  have hG' : |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P)| ≤
      K*(s : ℝ)*Real.sqrt s := by
    refine hG.trans ?_
    simp only [NNReal.coe_mul, hrcube]
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsr hs0)
      (show 0 ≤ (C₂ : ℝ)*(L : ℝ)^2/2 by positivity)
    dsimp [K,M₁,M₃] at *
    nlinarith only [ht]
  have hiF := boundedContinuousFunction_integrable_comp g.f hX
  have hiH := boundedContinuousFunction_integrable_comp (heatLogBCF s d g.f) hX
  change Integrable (fun ω => heatLog s d g.f (X ω)) P at hiH
  have hi₂ := boundedContinuousFunction_integrable_comp g.d2 hX
  have hi₁₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hX
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₁₂
  let R := fun ω => heatLog s d g.f (X ω) - g.f (X ω) -
    (s : ℝ)/2*(g.d2 (X ω)+(d : ℝ)*(g.d1 (X ω))^2)
  have hiR : Integrable R P := (hiH.sub hiF).sub ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
  have hR : |∫ ω, R ω ∂P| ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (f := R) (μ := P) (Filter.Eventually.of_forall fun ω =>
        show ‖R ω‖ ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s by
          simpa only [Real.norm_eq_abs, R] using hC g h₀ h₁ h₂ h₃ s hs (X ω))
  have hRe : (∫ ω, R ω ∂P) = (∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)) := by
    have he := integral_sub (hiH.sub hiF) ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
    simp only [Pi.sub_apply, Pi.add_apply] at he
    dsimp only [R]
    rw [he, integral_sub hiH hiF, integral_const_mul, integral_add hi₂ (hi₁₂.const_mul d), integral_const_mul]
  rw [hRe] at hR
  have hh := abs_sub
    ((∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P))
    ((∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)))
  have hh' := hh.trans (add_le_add hG' hR)
  convert! hh' using 1
  · congr 1; ring
  · change (K+(C : ℝ))*(s : ℝ)*Real.sqrt s = K*(s : ℝ)*Real.sqrt s + (C : ℝ)*(s : ℝ)*Real.sqrt s
    ring

lemma usualBrownianSigma_mono (P : Measure BrownianPath) {s t : Time} (hst : s ≤ t) :
    usualBrownianSigma P s ≤ usualBrownianSigma P t := by
  apply le_iInf
  intro r
  exact iInf_le_of_le (⟨r.val, lt_of_le_of_lt hst r.property⟩ : {r : ℝ≥0 // (s : ℝ) < r}) le_rfl

lemma brownianEval_usual_measurable (P : Measure BrownianPath) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (brownianEval ⟨t.val,t.property.1⟩) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro r
  apply le_sup_of_le_left
  exact le_iSup_of_le (⟨⟨t.val,t.property.1⟩, r.property.le⟩ : {s : ℝ≥0 // s ≤ r.val}) le_rfl

lemma progressive_prefix_integral_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
  let : MeasurableSpace BrownianPath := usualBrownianSigma P t
  have hm : Measurable (fun p : Set.Iic t × BrownianPath => a p.1.val * v p.1.val p.2) :=
    (ha.comp (measurable_subtype_coe.comp measurable_fst)).mul (hv t)
  have hi := hm.stronglyMeasurable.integral_prod_left (f := fun r ω => a r.val * v r.val ω) (μ := Measure.comap Subtype.val timeLaw)
  have he : (fun ω => ∫ r : Set.Iic t, a r.val * v r.val ω ∂Measure.comap Subtype.val timeLaw) =
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
    funext ω
    exact integral_subtype_comap (μ := timeLaw) (s := Set.Iic t) measurableSet_Iic (fun r => a r * v r ω)
  rw [he] at hi
  exact hi.measurable

lemma progressive_interval_integral_aemeasurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (s t : Time) :
    AEMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P := by
  have hm := (ha.comp measurable_fst).mul (progressive_joint_complete P hv)
  have hi := hm.stronglyMeasurable.integral_prod_left (β := NullMeasurableSpace BrownianPath P)
    (f := fun r ω => a r * v r ω) (μ := timeLaw.restrict (Set.Ioc s t))
  exact (show NullMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P from hi.measurable).aemeasurable

lemma controlledPrefix_usual_measurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) (controlledPrefix m v t) :=
  (brownianEval_usual_measurable P t).add (progressive_prefix_integral_measurable P hv m m.measurable t)

lemma timeSpan_coe {s t : Time} (hst : s ≤ t) :
    (timeSpan s t : ℝ) = (t : ℝ)-(s : ℝ) := Real.coe_toNNReal _ (sub_nonneg.mpr hst)

lemma timeSpan_le_one (s t : Time) : timeSpan s t ≤ 1 := by
  apply Real.toNNReal_le_one.mpr
  linarith [t.property.2,s.property.1]

lemma timeLaw_real_Ioc {s t : Time} (hst : s ≤ t) :
    timeLaw.real (Set.Ioc s t) = (t : ℝ)-(s : ℝ) := by
  simp only [timeLaw_eq_volume, Measure.real, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]

lemma timeLaw_integral_const_Ioc {s t : Time} (hst : s ≤ t) (a : ℝ) :
    (∫ _r in Set.Ioc s t, a ∂timeLaw) = ((t : ℝ)-(s : ℝ))*a := by
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, ← Measure.real,
    timeLaw_real_Ioc hst, smul_eq_mul]

lemma bounded_control_integrable (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    Integrable (fun r => m r * v r ω^2) timeLaw ∧ Integrable (fun r => m r * v r ω) timeLaw :=
  weightedTime_integrable m (progressive_time_measurable P hv ω)
    ((pathControlCost_le_bound m L hL ω).trans_lt (by finiteness))

lemma controlledPrefix_increment (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    controlledPrefix m v t ω = controlledPrefix m v s ω +
      (brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω) +
      ∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw := by
  have hi := (bounded_control_integrable P m L hv hL ω).2
  have he := setIntegral_union (s := Set.Iic s) (t := Set.Ioc s t)
    (Set.Iic_disjoint_Ioc (a := s) (c := t) le_rfl) measurableSet_Ioc
    hi.integrableOn hi.integrableOn
  rw [Set.Iic_union_Ioc_eq_Iic hst] at he
  unfold controlledPrefix
  rw [he]
  ring

lemma bounded_interval_drift (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    |∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw| ≤ (L : ℝ) * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm (L : ℝ)]
  calc
    _ ≤ ∫ r in Set.Ioc s t, |m r*v r ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ) ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).2.integrableOn.abs (integrable_const _)
      intro r
      change |m r * v r ω| ≤ (L : ℝ)
      rw [abs_mul, abs_of_nonneg (m.nonneg r)]
      exact (mul_le_mul_of_nonneg_left (hL r ω) (m.nonneg r)).trans
        (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst L

lemma intervalControlCost_nonneg (m : Trial) (v : Time → BrownianPath → ℝ) (s t : Time) (ω : BrownianPath) :
    0 ≤ intervalControlCost m v s t ω := integral_nonneg (fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))

lemma intervalControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time) :
    AEMeasurable (intervalControlCost m v s t) P :=
  progressive_interval_integral_aemeasurable P (fun r => (hv r).pow_const 2) m m.measurable s t

lemma intervalControlCost_le_bound (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    intervalControlCost m v s t ω ≤ (L : ℝ)^2 * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm ((L : ℝ)^2)]
  calc
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ)^2 ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).1.integrableOn (integrable_const _)
      intro r
      have hh : (v r ω)^2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) L.coe_nonneg).mpr (hL r ω)
      exact (mul_le_mul_of_nonneg_left hh (m.nonneg r)).trans (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst _

lemma intervalControlCost_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ t ω, |v t ω| ≤ L) {s t : Time} (hst : s ≤ t) :
    Integrable (intervalControlCost m v s t) P :=
  bounded_real_integrable (intervalControlCost_aemeasurable P m hv s t) ((L : ℝ)^2*timeSpan s t)
    (Filter.Eventually.of_forall fun ω => by
      rw [abs_of_nonneg (intervalControlCost_nonneg m v s t ω)]
      exact intervalControlCost_le_bound P m L hv hL hst ω)

lemma interval_square_completion (P : Measure BrownianPath) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (hm : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ))
    (a : ℝ) (ω : BrownianPath) :
    2*a*(∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw) -
      (d : ℝ)*(timeSpan s t : ℝ)*a^2 ≤ intervalControlCost m v s t ω := by
  have hi := bounded_control_integrable P m L hv hL ω
  have him : Integrable (fun r => m r) timeLaw := by
    apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (m.nonneg r)]; exact m.le_one r
  have hmono := setIntegral_mono_on (s := Set.Ioc s t) ((hi.2.const_mul (2*a)).sub (him.const_mul (a^2))).integrableOn
    hi.1.integrableOn measurableSet_Ioc (fun r _ => by
      change 2*a*(m r*v r ω) - a^2*m r ≤ m r*(v r ω)^2
      nlinarith [mul_nonneg (m.nonneg r) (sq_nonneg (v r ω-a))])
  have he : (∫ r in Set.Ioc s t, m r ∂timeLaw) = (d : ℝ)*timeSpan s t := by
    rw [setIntegral_congr_fun measurableSet_Ioc hm, timeLaw_integral_const_Ioc hst, timeSpan_coe hst, mul_comm]
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hi.2.const_mul (2*a)).integrableOn (him.const_mul (a^2)).integrableOn,
    integral_const_mul, integral_const_mul, he] at hmono
  convert! hmono using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma brownian_increment_timeSpan (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {s t : Time} (hst : s ≤ t) :
    HasLaw (fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω)
      (gaussianReal 0 (timeSpan s t)) P := by
  have he : timeSpan s t = nndist (t : ℝ) (s : ℝ) := by
    apply NNReal.coe_injective
    rw [timeSpan_coe hst, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
  rw [he]
  exact (hB.toIsPreBrownianReal.hasLaw_sub ⟨t.val,t.property.1⟩ ⟨s.val,s.property.1⟩).congr
    (Filter.Eventually.of_forall fun ω => rfl)

lemma brownian_control_cell_upper (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) ≤
        (∫ ω, intervalControlCost m v s t ω ∂P)/2 +
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃
  let X := controlledPrefix m v s
  let Z := fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω
  let A := fun ω => ∫ r in Set.Ioc s t, m r*v r ω ∂timeLaw
  have hX := controlledPrefix_usual_measurable P m hv s
  have hXm : AEMeasurable X P := usual_measurable_aemeasurable P s hX
  have hAm : AEMeasurable A P := progressive_interval_integral_aemeasurable P hv m m.measurable s t
  have hAb : ∀ ω, |A ω| ≤ (L : ℝ)*timeSpan s t := bounded_interval_drift P m L hv hL hst.le
  have he := hC P g h₀ h₁ h₂ h₃ (timeSpan s t) (timeSpan_le_one s t) X Z A hXm
    (brownian_increment_timeSpan P hB hst.le)
    (brownian_increment_indep_adapted P hB s ⟨t.val,t.property.1⟩ hst hX) hAm hAb
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := by
    intro ω
    exact (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hi₁ := boundedContinuousFunction_integrable_comp g.d1 hXm
  have hi₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hXm
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₂
  have hiA := bounded_real_integrable hAm ((L : ℝ)*timeSpan s t) (Filter.Eventually.of_forall hAb)
  have hiJ : Integrable (fun ω => g.d1 (X ω)*A ω) P :=
    hiA.bdd_mul ((g.d1.continuous.measurable.comp_aemeasurable hXm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => g.d1.norm_coe_le_norm (X ω))
  have hq := integral_mono ((hiJ.const_mul 2).sub (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))))
    (intervalControlCost_integrable P m L hv hL hst.le)
    (fun ω => by
      change 2*(g.d1 (X ω)*A ω) - (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 ≤ _
      nlinarith only [interval_square_completion P m L d hv hL hst.le hm (g.d1 (X ω)) ω])
  simp only [Pi.sub_apply] at hq
  rw [integral_sub (hiJ.const_mul 2) (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))),
    integral_const_mul, integral_const_mul] at hq
  exact le_trans (by linarith only [(abs_le.mp he).2,hq]) le_rfl

lemma antitoneOn_of_superlinear_increment (F : Time → ℝ) (C : ℝ)
    {a b : Time} (hab : a ≤ b)
    (h : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt ((t : ℝ)-(s : ℝ))) : F b ≤ F a := by
  have hbnd : ∀ n : ℕ, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt (((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro s hs t ht hst
      have hstreal : (s : ℝ) < (t : ℝ) := hst
      let u : Time := ⟨((s : ℝ)+(t : ℝ))/2, by
        constructor <;> linarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
      have hsu : s < u := by change (s : ℝ) < ((s : ℝ)+(t : ℝ))/2; linarith only [hstreal]
      have hut : u < t := by change ((s : ℝ)+(t : ℝ))/2 < (t : ℝ); linarith only [hstreal]
      have hu : u ∈ Set.Icc a b := ⟨hs.1.trans hsu.le,hut.le.trans ht.2⟩
      have h₁ := ih s hs u hu hsu
      have h₂ := ih u hu t ht hut
      have e₁ : (u : ℝ)-(s : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      have e₂ : (t : ℝ)-(u : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      rw [e₁] at h₁
      rw [e₂] at h₂
      have e₃ : ((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^(n+1) = (((t : ℝ)-(s : ℝ))/2)*(1/2 : ℝ)^n := by rw [pow_succ]; ring
      rw [e₃]
      linarith only [h₁,h₂]
  rcases hab.eq_or_lt with heq | hlt
  · simp [heq]
  have hlim : Tendsto (fun n : ℕ => C*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))*(1/2 : ℝ)^n)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    simpa using (hp.const_mul ((b : ℝ)-(a : ℝ))).sqrt.const_mul (C*((b : ℝ)-(a : ℝ)))
  have he := ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hbnd n a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hlt)
  linarith only [he]

lemma timeSpan_add {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    timeSpan a b + timeSpan b c = timeSpan a c := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add,timeSpan_coe hab,timeSpan_coe hbc,timeSpan_coe (hab.trans hbc)]
  ring

lemma intervalControlCost_add (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) (ω : BrownianPath) :
    intervalControlCost m v a c ω = intervalControlCost m v a b ω + intervalControlCost m v b c ω := by
  have hi := (bounded_control_integrable P m L hv hL ω).1
  have he := setIntegral_union (s := Set.Ioc a b) (t := Set.Ioc b c)
    (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi.integrableOn hi.integrableOn
  rwa [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at he

lemma expected_intervalControlCost_add (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ r ω, |v r ω| ≤ L) {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ ω, intervalControlCost m v a c ω ∂P) =
      (∫ ω, intervalControlCost m v a b ω ∂P) + (∫ ω, intervalControlCost m v b c ω ∂P) := by
  simp only [intervalControlCost_add P m L hv hL hab hbc]
  exact integral_add (intervalControlCost_integrable P m L hv hL hab)
    (intervalControlCost_integrable P m L hv hL hbc)

lemma brownian_control_interval_upper (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b : Time} (hab : a ≤ b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) (g : Jet3) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) ≤
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  obtain ⟨C,hC⟩ := brownian_control_cell_upper d L C₀ C₁ C₂ C₃
  let F : Time → ℝ := fun t =>
    (∫ ω, heatLog (timeSpan t b) d g.f (controlledPrefix m v t ω) ∂P) -
      (∫ ω, intervalControlCost m v a t ω ∂P)/2
  have hF := antitoneOn_of_superlinear_increment F (C : ℝ) hab (by
    intro s hs t ht hst
    have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
    obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
    have hh := hC P hB m v hv hL s t hst hmst (g.heatLog (timeSpan t b) d) h₀ h₁ h₂ h₃
    rw [g.heatLog_f] at hh
    simp only [heatLogBCF_coe, heatLog_semigroup, timeSpan_add hst.le ht.2] at hh
    have hcost := expected_intervalControlCost_add P m L hv hL hs.1 hst.le
    rw [timeSpan_coe hst.le] at hh
    dsimp [F]
    linarith only [hh,hcost])
  have he₁ : timeSpan b b = 0 := by simp [timeSpan]
  have he₂ : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  dsimp [F] at hF
  simp only [he₁,heatLog_zero,he₂,integral_zero,zero_div,sub_zero] at hF
  linarith only [hF]

lemma progressive_patchControl (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time)
    {a : BrownianPath → ℝ} (ha : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) a) :
    Progressive P (patchControl v s t a) := by
  intro T
  by_cases hs : s ≤ T
  · have haT := ha.mono (usualBrownianSigma_mono P hs) le_rfl
    apply Measurable.ite _ (haT.comp measurable_snd) (hv T)
    exact (measurableSet_Ioc : MeasurableSet (Set.Ioc s t)).preimage
      (measurable_subtype_coe.comp measurable_fst)
  · have he : (fun p : Set.Iic T × BrownianPath => patchControl v s t a p.1.val p.2) =
        (fun p : Set.Iic T × BrownianPath => v p.1.val p.2) := by
      funext p
      apply ite_eq_right
      intro h
      exact hs (h.1.le.trans p.1.property)
    rw [he]
    exact hv T

lemma patchControl_bound {v : Time → BrownianPath → ℝ} {L : ℝ≥0}
    (hv : ∀ r ω, |v r ω| ≤ L) (s t : Time) {a : BrownianPath → ℝ}
    (ha : ∀ ω, |a ω| ≤ L) : ∀ r ω, |patchControl v s t a r ω| ≤ L := by
  intro r ω
  simp only [patchControl]
  split <;> first | exact ha ω | exact hv r ω

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianAffineCoordinate
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

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma stdGaussian_coordinate_law (i : I) :
    (stdGaussian (EuclideanSpace ℝ I)).map (fun x => x i)=gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ => gaussianReal 0 1) i).map_eq

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BackwardScore
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma patchControl_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    controlledPrefix m (patchControl v s t a) r ω = controlledPrefix m v r ω := by
  unfold controlledPrefix
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma patchControl_cost_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) (q : Time) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    intervalControlCost m (patchControl v s t a) q r ω = intervalControlCost m v q r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.2.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma brownian_control_feedback_cell (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∀ r ∈ Set.Ioc s t, ∀ ω, v r ω = g.d1 (controlledPrefix m v s ω)) →
      |(∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) -
        (∫ ω, intervalControlCost m v s t ω ∂P)/2| ≤
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃ hV
  let X := controlledPrefix m v s
  let Z := fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω
  let A := fun ω => ∫ r in Set.Ioc s t, m r*v r ω ∂timeLaw
  have hX := controlledPrefix_usual_measurable P m hv s
  have hXm : AEMeasurable X P := usual_measurable_aemeasurable P s hX
  have hAm : AEMeasurable A P := progressive_interval_integral_aemeasurable P hv m m.measurable s t
  have hAb : ∀ ω, |A ω| ≤ (L : ℝ)*timeSpan s t := bounded_interval_drift P m L hv hL hst.le
  have he := hC P g h₀ h₁ h₂ h₃ (timeSpan s t) (timeSpan_le_one s t) X Z A hXm
    (brownian_increment_timeSpan P hB hst.le)
    (brownian_increment_indep_adapted P hB s ⟨t.val,t.property.1⟩ hst hX) hAm hAb
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := fun ω =>
    (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hA : ∀ ω, A ω = (d : ℝ)*(timeSpan s t : ℝ)*g.d1 (X ω) := by
    intro ω
    dsimp only [A]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hQ : ∀ ω, intervalControlCost m v s t ω =
      (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 := by
    intro ω
    rw [intervalControlCost,setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hJ : (∫ ω, g.d1 (X ω)*A ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hA]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by ring
  have hQi : (∫ ω, intervalControlCost m v s t ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hQ,integral_const_mul]
  rw [hJ] at he
  rw [hQi]
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma brownian_control_patch_gain (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ (v : Time → BrownianPath → ℝ), Progressive P v →
      (∀ r ω, |v r ω| ≤ L) → ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc s t, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g s - (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) ≤
          backwardScore P m w a b d g t := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  let L := max L₀ C₁
  obtain ⟨C,hC⟩ := brownian_control_feedback_cell d L C₀ C₁ C₂ C₃
  refine ⟨L,C,le_max_left _ _,?_⟩
  intro v hv hL s hs t ht hst
  let j := g.heatLog (timeSpan t b) d
  let A := fun ω => j.d1 (controlledPrefix m v s ω)
  have hAm : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) A :=
    j.d1.continuous.measurable.comp (controlledPrefix_usual_measurable P m hv s)
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
  have hAL : ∀ ω, |A ω| ≤ L := fun ω =>
    ((j.d1.norm_coe_le_norm _).trans h₁).trans (show (C₁ : ℝ) ≤ L from le_max_right _ _)
  let w := patchControl v s t A
  have hw : Progressive P w := progressive_patchControl P hv s t hAm
  have hwL : ∀ r ω, |w r ω| ≤ L := patchControl_bound hL s t hAL
  have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
  have hXe : ∀ ω, controlledPrefix m w s ω = controlledPrefix m v s ω :=
    patchControl_prefix m v s t A le_rfl
  have hQe : ∀ ω, intervalControlCost m w a s ω = intervalControlCost m v a s ω :=
    patchControl_cost_prefix m v s t A a le_rfl
  have hfeedback : ∀ r ∈ Set.Ioc s t, ∀ ω, w r ω = j.d1 (controlledPrefix m w s ω) := by
    intro r hr ω
    rw [hXe]
    exact ite_eq_left hr
  have hh := hC P hB m w hw hwL s t hst hmst j h₀ h₁ h₂ h₃ hfeedback
  change |(∫ ω, (g.heatLog (timeSpan t b) d).f (controlledPrefix m w t ω) ∂P) - _ - _| ≤ _ at hh
  rw [g.heatLog_f] at hh
  simp only [heatLogBCF_coe,heatLog_semigroup,timeSpan_add hst.le ht.2,hXe] at hh
  have hcost := expected_intervalControlCost_add P m L hw hwL hs.1 hst.le
  simp only [hQe] at hcost
  refine ⟨w,hw,hwL,?_,?_⟩
  · intro r hr ω
    exact ite_eq_right hr
  · dsimp [backwardScore]
    linarith only [(abs_le.mp hh).1,hcost]

lemma timeMesh_coe (a b : Time) (n k : ℕ) (hk : k ≤ n+1) :
    (timeMesh a b n k : ℝ) = (a : ℝ)+((b : ℝ)-(a : ℝ))*((k : ℝ)/(n+1)) := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hh : (k : ℝ)/(n+1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hp).mpr
      exact_mod_cast hk
  simp only [timeMesh, Set.projIcc_of_mem zero_le_one hh, Set.Icc.coe_convexComb]
  ring

lemma timeMesh_zero (a b : Time) (n : ℕ) : timeMesh a b n 0 = a := by
  apply Subtype.ext
  rw [timeMesh_coe a b n 0 (Nat.zero_le _)]
  simp

lemma timeMesh_last (a b : Time) (n : ℕ) : timeMesh a b n (n+1) = b := by
  apply Subtype.ext
  rw [timeMesh_coe a b n (n+1) le_rfl]
  push_cast
  rw [div_self (by positivity : (n : ℝ)+1 ≠ 0)]
  ring

lemma timeMesh_between {a b : Time} (hab : a ≤ b) (n k : ℕ) (hk : k ≤ n+1) :
    timeMesh a b n k ∈ Set.Icc a b := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hq : 0 ≤ (k : ℝ)/(n+1) := by positivity
  have hr : (k : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr (by exact_mod_cast hk)
  have habr : (a : ℝ) ≤ (b : ℝ) := hab
  constructor <;> change _ ≤ (show ℝ from ↑_)
  · rw [timeMesh_coe a b n k hk]
    nlinarith
  · rw [timeMesh_coe a b n k hk]
    nlinarith

lemma timeMesh_step {a b : Time} (hab : a < b) (n k : ℕ) (hk : k < n+1) :
    timeMesh a b n k < timeMesh a b n (k+1) := by
  change (timeMesh a b n k : ℝ) < (timeMesh a b n (k+1) : ℝ)
  rw [timeMesh_coe a b n k hk.le, timeMesh_coe a b n (k+1) hk]
  have hh : (a : ℝ) < (b : ℝ) := hab
  have hp : (0 : ℝ) < n+1 := by positivity
  apply add_lt_add_of_le_of_lt le_rfl
  apply mul_lt_mul_of_pos_left _ (sub_pos.mpr hh)
  apply div_lt_div_of_pos_right _ hp
  exact_mod_cast Nat.lt_succ_self k

lemma timeMesh_step_size (a b : Time) (n k : ℕ) (hk : k < n+1) :
    (timeMesh a b n (k+1) : ℝ) - (timeMesh a b n k : ℝ) = ((b : ℝ)-(a : ℝ))/(n+1) := by
  rw [timeMesh_coe a b n k hk.le,timeMesh_coe a b n (k+1) hk]
  push_cast
  ring

lemma brownian_control_interval_lower_mesh (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ n : ℕ,
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) -
          (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,hLL,hgain⟩ := brownian_control_patch_gain P hB m d L₀ g hm
  refine ⟨L,C,hLL,?_⟩
  intro n
  let τ := timeMesh a b n
  let δ : ℝ := ((b : ℝ)-(a : ℝ))/(n+1)
  let E : ℝ := (C : ℝ)*δ*Real.sqrt δ
  have hind : ∀ k : ℕ, k ≤ n+1 →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g a - (k : ℝ)*E ≤ backwardScore P m w a b d g (τ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨v,hv,fun r ω => (hvL r ω).trans (show (L₀ : ℝ) ≤ L from hLL),?_,?_⟩
      · intro _ _ _; rfl
      · simp only [τ,timeMesh_zero,Nat.cast_zero,zero_mul,sub_zero,le_refl]
    | succ k ih =>
      intro hk
      obtain ⟨u,hu,huL,huout,huScore⟩ := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hk' : k < n+1 := hk
      have hs := timeMesh_between hab.le n k hk'.le
      have ht := timeMesh_between hab.le n (k+1) hk
      have hst := timeMesh_step hab n k hk'
      obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hgain u hu huL (τ k) hs (τ (k+1)) ht hst
      have heδ : (timeSpan (τ k) (τ (k+1)) : ℝ) = δ := by
        rw [timeSpan_coe hst.le]
        exact timeMesh_step_size a b n k hk'
      rw [heδ] at hwScore
      refine ⟨w,hw,hwL,?_,?_⟩
      · intro r hr ω
        have hr' : r ∉ Set.Ioc (τ k) (τ (k+1)) := fun hh =>
          hr ⟨hs.1.trans_lt hh.1,hh.2.trans ht.2⟩
        rw [hwout r hr' ω]
        exact huout r hr ω
      · change backwardScore P m u a b d g (τ k) - E ≤ _ at hwScore
        rw [Nat.cast_succ]
        linarith only [huScore,hwScore]
  obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hind (n+1) le_rfl
  have he : ((n+1 : ℕ) : ℝ)*E =
      (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) := by
    dsimp [E,δ]
    push_cast
    field_simp
  have hz : timeSpan b b = 0 := by simp [timeSpan]
  have hq : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  simp only [τ,timeMesh_last,he,backwardScore,hz,heatLog_zero,hq,integral_zero,zero_div,sub_zero] at hwScore
  exact ⟨w,hw,hwL,hwout,hwScore⟩

lemma brownian_control_interval_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,_,hmesh⟩ := brownian_control_interval_lower_mesh P hB m d L₀ g hab hm v hv hvL
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => ((b : ℝ)-(a : ℝ))/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have he : Tendsto (fun n : ℕ => (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)))
      atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hd).const_mul ((C : ℝ)*((b : ℝ)-(a : ℝ)))
  obtain ⟨n,hn⟩ := (he.eventually (gt_mem_nhds hε)).exists
  obtain ⟨w,hw,hwL,hwout,hwval⟩ := hmesh n
  exact ⟨L,w,hw,hwL,hwout,by linarith⟩

lemma HeatChain.left_le_right {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) : a ≤ b := by
  cases H with
  | nil => exact le_rfl
  | cons _ hat htb _ _ => exact hat.le.trans htb

lemma controls_equal_cost_prefix {m : Trial} {v w : Time → BrownianPath → ℝ} {a b r s : Time}
    (h : ∀ t ∉ Set.Ioc a b, ∀ ω, w t ω = v t ω) (hr : r ≤ a) (ω : BrownianPath) :
    intervalControlCost m w s r ω = intervalControlCost m v s r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [h t (fun hh => not_lt_of_ge (ht.2.trans hr) hh.1) ω]

lemma HeatChain.upper {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 ≤
        (∫ ω, h.f (controlledPrefix m v a ω) ∂P) := by
  induction H with
  | nil a => simp [intervalControlCost]
  | @cons a t b h d hat htb hm tail ih =>
    have hi := brownian_control_interval_upper P hB m L d hv hL hat.le hm h
    have hc := expected_intervalControlCost_add P m L hv hL hat.le htb
    rw [Jet3.heatLog_f]
    simp only [heatLogBCF_coe]
    linarith only [ih,hi,hc]

lemma HeatChain.lower {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ K) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, h.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  induction H generalizing v L ε with
  | nil a =>
    refine ⟨L,v,hv,hL,fun _ _ _ => rfl,?_⟩
    simp only [intervalControlCost,Set.Ioc_self,Measure.restrict_empty,integral_zero_measure,
      integral_zero,zero_div,sub_zero]
    linarith
  | @cons a t b h d hat htb hm tail ih =>
    obtain ⟨K,u,hu,huK,huout,huval⟩ :=
      brownian_control_interval_lower P hB m d L h hat hm v hv hL (by positivity : 0 < ε/2)
    obtain ⟨K',w,hw,hwK,hwout,hwval⟩ := ih K u hu huK (by positivity : 0 < ε/2)
    have hc := expected_intervalControlCost_add P m K' hw hwK hat.le htb
    have he : ∀ ω, intervalControlCost m w a t ω = intervalControlCost m u a t ω :=
      controls_equal_cost_prefix hwout le_rfl
    simp only [he] at hc
    refine ⟨K',w,hw,hwK,?_,?_⟩
    · intro r hr ω
      rw [hwout r (fun hh => hr ⟨hat.trans hh.1,hh.2⟩) ω]
      exact huout r (fun hh => hr ⟨hh.1,hh.2.trans htb⟩) ω
    · rw [Jet3.heatLog_f]
      simp only [heatLogBCF_coe]
      linarith only [huval,hwval,hc]

lemma controlledPrefix_one (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    controlledPrefix m v 1 ω = brownianEval 1 ω + controlDrift m v ω := by
  simp only [controlledPrefix,controlDrift,show Set.Iic (1 : Time) = Set.univ from Set.Iic_top,
    Measure.restrict_univ]
  rfl

lemma controlledPrefix_zero (P : Measure BrownianPath) (hB : IsBrownianReal brownianEval P)
    (m : Trial) (v : Time → BrownianPath → ℝ) : controlledPrefix m v 0 =ᵐ[P] fun _ => 0 := by
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  simp only [controlledPrefix,show Set.Iic (0 : Time) = {0} from Set.Iic_bot,
    Measure.restrict_singleton,measure_singleton,zero_smul,integral_zero_measure,add_zero]
  exact hω

lemma intervalControlCost_full (m : Trial) (v : Time → BrownianPath → ℝ)
    (ω : BrownianPath) (hm : Measurable (v · ω)) :
    intervalControlCost m v 0 1 ω = (pathControlCost m v ω).toReal := by
  unfold intervalControlCost
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := timeLaw)), show Set.Icc (0 : Time) 1 = Set.univ from Set.Icc_bot_top,
    Measure.restrict_univ]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))
    ((m.measurable.mul (hm.pow_const 2)).aestronglyMeasurable)

lemma expected_intervalControlCost_full (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, intervalControlCost m v 0 1 ω ∂P) = (controlCost P m v).toReal := by
  simp only [intervalControlCost_full m v _ (progressive_time_measurable P hv _)]
  exact integral_pathControlCost P m hv hc

lemma Jet3.lipschitz (g : Jet3) : LipschitzWith ‖g.d1‖₊ g.f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (g.has1 x).differentiableAt)
  intro x
  rw [g.deriv_eq]
  exact_mod_cast g.d1.norm_coe_le_norm x

lemma HeatChain.controlValue_eq {m : Trial} {g h : Jet3}
    (H : HeatChain m g 0 1 h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) : controlValue P g.f m = h.f 0 := by
  apply le_antisymm
  · apply controlValue_le_of_bounded_controls P g.f m ‖g.d1‖₊ g.lipschitz
    intro v hv hc hL
    have hh := H.upper P hB ‖g.d1‖₊ hv hL
    have he : (∫ ω, h.f (controlledPrefix m v 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m v] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hv hc] at hh
    simp only [controlledPrefix_one] at hh
    exact hh
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨K,w,hw,hwK,_,hwval⟩ := H.lower P hB 0 (fun _ _ => 0) (progressive_zero P)
      (by simp) hε
    have hc : controlCost P m w < ∞ := (controlCost_le_bound P m K hwK).trans_lt (by finiteness)
    have he : (∫ ω, h.f (controlledPrefix m (fun _ _ => 0) 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m (fun _ _ => 0)] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hw hc] at hwval
    simp only [controlledPrefix_one] at hwval
    have hsup : controlPayoff P g.f m w ≤ controlValue P g.f m :=
      le_csSup (controlPayoffs_bddAbove P g.f m) ⟨w,hw,hc,rfl⟩
    change h.f 0 - ε ≤ controlPayoff P g.f m w at hwval
    linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma Jet3.eq_of_f_eq {g h : Jet3} (he : g.f=h.f) : g=h := by
  have h1 : g.d1=h.d1 := by
    ext x
    rw [← g.deriv_eq,← h.deriv_eq,he]
  have h2 : g.d2=h.d2 := by
    ext x
    rw [← g.deriv2_eq,← h.deriv2_eq,he]
  have h3 : g.d3=h.d3 := by
    ext x
    rw [← g.deriv3_eq,← h.deriv3_eq,he]
  cases g
  cases h
  simp_all

lemma Jet3.heatLog_zero_time (g : Jet3) (d : ℝ≥0) : g.heatLog 0 d=g := by
  apply Jet3.eq_of_f_eq
  ext x
  simp only [Jet3.heatLog_f,heatLogBCF_coe,heatLog_zero]

lemma finiteStepControlJet_chain (g : Jet3) (m : Trial) (n : ℕ)
    (q : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q)
    (hm : ∀ i : Fin n, ∀ r∈Ioc (q i.castSucc) (q i.succ), m r=(d i:ℝ)) :
    HeatChain m g (q 0) (q (Fin.last n)) (finiteStepControlJet g n q d) := by
  induction n with
  | zero => exact HeatChain.nil (q 0)
  | succ n ih =>
    have ih' := ih (fun i => q i.succ) (fun i => d i.succ)
      (hq.comp (Fin.strictMono_succ.monotone)) (fun i => hm i.succ)
    change HeatChain m g (q 1) (q (Fin.last (n+1))) _ at ih'
    have h01 : q 0≤q 1 := hq (Fin.zero_le _)
    rcases lt_or_eq_of_le h01 with hlt | he
    · exact HeatChain.cons (d 0) hlt (hq (Fin.le_last _)) (hm 0) ih'
    · simpa only [finiteStepControlJet,he,timeSpan,sub_self,Real.toNNReal_zero,
        Jet3.heatLog_zero_time] using ih'

lemma leftWeightedStepTrial_ae {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    (leftWeightedStepTrial w q hw hw1 : Time→ℝ)=ᵐ[timeLaw] weightedStepTrial w q hw hw1 := by
  have he : ∀ᵐ t ∂timeLaw, ∀ i, t≠q i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_iff.mpr
    simp
  filter_upwards [he] with t ht
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i≤t
  · rw [ite_eq_left hi,ite_eq_left (lt_of_le_of_ne hi (Ne.symm (ht i)))]
  · rw [ite_eq_right hi,ite_eq_right (not_lt_of_ge (le_of_not_ge hi))]

lemma leftWeightedStepTrial_interval (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (i : Fin n) {r : Time} (hr : r∈Ioc (q i.castSucc) (q i.succ)) :
    leftWeightedStepTrial w q hw hw1 r=(weightedControlCoefficient n w hw i:ℝ) := by
  change (∑ j, if q j < r then w j else 0) = ∑ j, if j ≤ i.castSucc then w j else 0
  apply Finset.sum_congr rfl
  intro j _
  have he : q j < r ↔ j ≤ i.castSucc := by
    constructor
    · intro hj
      by_contra hn
      have hij : i.succ ≤ j := by
        simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hn ⊢
        omega
      exact not_lt_of_ge ((hq hij).trans' hr.2) hj
    · intro hj
      exact (hq hj).trans_lt hr.1
  simp only [he]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_LabelProfileControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma oneDim_inner (v : EuclideanSpace ℝ (Fin 1)) :
    inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v=v 0 := by
  simp [PiLp.inner_apply]

lemma oneDim_gaussian_average (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (a : ℝ) :
    (∫ v : EuclideanSpace ℝ (Fin 1), f (a+Real.sqrt s*v 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))=gaussianAverage s f a := by
  rw [gaussianAverage_scaling]
  have h : (∫ z, f (a+Real.sqrt s*z) ∂((stdGaussian (EuclideanSpace ℝ (Fin 1))).map
      (fun v => v 0)))=∫ v : EuclideanSpace ℝ (Fin 1), f (a+Real.sqrt s*v 0)
        ∂stdGaussian (EuclideanSpace ℝ (Fin 1)) :=
    integral_map (show Measurable (fun v : EuclideanSpace ℝ (Fin 1) => v 0) from by fun_prop).aemeasurable
      (show Measurable (fun z : ℝ => f (a+Real.sqrt s*z)) from by fun_prop).aestronglyMeasurable
  rw [stdGaussian_coordinate_law] at h
  exact h.symm

lemma oneDim_gaussian_entropic (s b : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ (Fin 1))) b
      (diagonalMark (fun _ => Real.sqrt s)) (fun v => f (v 0)) x=heatLog s b f (x 0) := by
  have hX : ∀ a : ℝ, Integrable
      (fun v : EuclideanSpace ℝ (Fin 1) => Real.exp (a*f (x 0+Real.sqrt s*v 0)))
      (stdGaussian (EuclideanSpace ℝ (Fin 1))) := fun a =>
    boundedContinuousFunction_integrable_comp (expBCF a f) (by fun_prop)
  change entropicMean (stdGaussian (EuclideanSpace ℝ (Fin 1))) b
    (fun v => f (x 0+Real.sqrt s*v 0))=heatLog s b f (x 0)
  by_cases hb : b=0
  · subst b
    rw [NNReal.coe_zero,entropicMean_zero _ hX,heatLog,ite_eq_left rfl,oneDim_gaussian_average]
  · rw [entropicMean_eq_div _ hX (by exact_mod_cast hb),heatLog,ite_eq_right hb]
    unfold cgf mgf
    change Real.log (∫ v : EuclideanSpace ℝ (Fin 1), expBCF b f (x 0+Real.sqrt s*v 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))/(b:ℝ)=_
    rw [oneDim_gaussian_average]
    ring

lemma linearCascadeWord_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : ℕ→E→L[ℝ] E) (k : ℕ) (z : Fin k→ℝ) (h : ∀ j<k,A j=B j) :
    linearCascadeWord A k z=linearCascadeWord B k z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [linearCascadeWord]
    rw [h k (Nat.lt_succ_self k),ih (fun i => z i.succ) (fun j hj => h j (Nat.lt_succ_of_lt hj))]

lemma profileGaussianStep_first {k : ℕ} (q : Fin (k+2)→Time) :
    profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) k=
      fun _ => Real.sqrt (timeSpan (q 0) (q 1)) := by
  funext i
  simp only [profileGaussianStep,dite_eq_left (Nat.lt_succ_self k)]
  have h0 : (⟨k+1-k-1,by omega⟩ : Fin (k+2))=0 := by ext; simp
  have h1 : (⟨k+1-k,by omega⟩ : Fin (k+2))=1 := by ext; simp
  rw [h0,h1]
  simp only [timeSpan,Real.coe_toNNReal']
  by_cases h : 0≤(q 1:ℝ)-q 0
  · rw [max_eq_left h]
  · have hn : (q 1:ℝ)-q 0≤0 := by linarith
    rw [max_eq_right hn,Real.sqrt_eq_zero_of_nonpos hn,Real.sqrt_zero]

lemma profileGaussianStep_tail {k : ℕ} (q : Fin (k+2)→Time) {j : ℕ} (hj : j<k) :
    profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j=
      profileGaussianStep (fun l (_ : Fin 1) => (q l.succ:ℝ)) j := by
  funext i
  simp only [profileGaussianStep,dite_eq_left hj,dite_eq_left (Nat.lt_succ_of_lt hj)]
  have ha : (⟨k+1-j,by omega⟩ : Fin (k+2))=(⟨k-j,by omega⟩ : Fin (k+1)).succ := by
    ext; simp only [Fin.val_succ]; omega
  have hb : (⟨k+1-j-1,by omega⟩ : Fin (k+2))=(⟨k-j-1,by omega⟩ : Fin (k+1)).succ := by
    ext; simp only [Fin.val_succ]; omega
  rw [ha,hb]

lemma oneDim_profile_backward (g : Jet3) (k : ℕ) (q : Fin (k+1)→Time)
    (z : Fin k→ℝ≥0) (x : EuclideanSpace ℝ (Fin 1)) :
    gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
      (linearCascadeWord (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j))
        k (fun i => z i)) (fun v => g.f (v 0)) x=(finiteStepControlJet g k q z).f (x 0) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [linearCascadeWord,gaussianLinearBackward,finiteStepControlJet]
    rw [profileGaussianStep_first]
    have hw := linearCascadeWord_congr
      (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j))
      (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l.succ:ℝ)) j))
      k (fun i => (z i.succ:ℝ)) (fun j hj => congrArg diagonalMark (profileGaussianStep_tail q hj))
    rw [hw]
    have hf := funext (ih (fun i => q i.succ) (fun i => z i.succ))
    rw [hf,oneDim_gaussian_entropic,Jet3.heatLog_f]
    change _=heatLog _ _ _ _
    rfl

lemma HeatChain.prepend {m : Trial} {g h j : Jet3} {a b c : Time}
    (H : HeatChain m g b c h) (J : HeatChain m h a b j) : HeatChain m g a c j := by
  induction J with
  | nil => exact H
  | cons d hat htb hm tail ih =>
    exact HeatChain.cons d hat (htb.trans H.left_le_right) hm (ih H)

lemma weightedStepTrial_controlValue_core (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w q hw hw1)=
      ((finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
        (weightedControlCoefficient k w hw)).heatLog (timeSpan 0 (q 0)) 0).f 0 := by
  let m := leftWeightedStepTrial w q hw hw1
  have ht : HeatChain m g (q (Fin.last k)) 1 (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) := by
    rcases lt_or_eq_of_le (show q (Fin.last k)≤1 from le_top) with hl|he
    · apply HeatChain.cons 1 hl le_rfl _ (HeatChain.nil 1)
      intro r hr
      change (∑ i, if q i < r then w i else 0)=(1:ℝ)
      have hqr i : q i < r := (hq (Fin.le_last i)).trans_lt hr.1
      simp only [hqr,ite_true,hw1]
    · rw [he]
      simp only [timeSpan,sub_self,Real.toNNReal_zero,Jet3.heatLog_zero_time]
      exact HeatChain.nil 1
  have hm := finiteStepControlJet_chain (g.heatLog (timeSpan (q (Fin.last k)) 1) 1)
    m k q (weightedControlCoefficient k w hw) hq
    (fun i r hr => leftWeightedStepTrial_interval k w q hw hw1 hq i hr)
  have hm' := ht.prepend hm
  have H : HeatChain m g 0 1 ((finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1)
      k q (weightedControlCoefficient k w hw)).heatLog (timeSpan 0 (q 0)) 0) := by
    rcases lt_or_eq_of_le (show (0:Time)≤q 0 from bot_le) with hl|he
    · apply HeatChain.cons 0 hl (show q 0≤1 from le_top) _ hm'
      intro r hr
      change (∑ i, if q i < r then w i else 0)=(0:ℝ)
      have hqr i : ¬ q i < r := not_lt_of_ge (hr.2.trans (hq (Fin.zero_le i)))
      simp only [hqr,ite_false,Finset.sum_const_zero]
    · rw [←he] at hm' ⊢
      simpa only [timeSpan,sub_self,Real.toNNReal_zero,Jet3.heatLog_zero_time] using hm'
  have he := leftWeightedStepTrial_ae w q hw hw1
  have hv := controlValue_trial_abs_sub_le P g.f (weightedStepTrial w q hw hw1) m ‖g.d1‖₊ g.lipschitz
  have hz : (∫ t, |weightedStepTrial w q hw hw1 t-m t| ∂timeLaw)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with t ht
    simp only [m,ht,sub_self,abs_zero,Pi.zero_apply]
  rw [hz,mul_zero] at hv
  rw [sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))]
  exact H.controlValue_eq P hB

theorem labelProfileValue_control (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    labelProfileValue k (stepCumulative w) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g=
      controlValue P g.f (weightedStepTrial w q hw hw1) := by
  rw [weightedStepTrial_controlValue_core k w q hw hw1 hq g P hB]
  have hend : (⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0)=
      timeSpan (q (Fin.last k)) 1 := by
    apply Subtype.ext
    change 1-(q (Fin.last k):ℝ)=(timeSpan (q (Fin.last k)) 1:ℝ)
    exact (timeSpan_coe (show q (Fin.last k)≤1 from le_top)).symm
  have hstart : (timeSpan 0 (q 0):ℝ)=(q 0:ℝ) := by
    rw [timeSpan_coe (show (0:Time)≤q 0 from bot_le)]; simp
  have hterm : labelProfileTerminal g (timeSpan (q (Fin.last k)) 1)=
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog (timeSpan (q (Fin.last k)) 1) 1).f (v 0) := by
    funext v
    rw [labelProfileTerminal,oneDim_inner,Jet3.heatLog_f]
    rfl
  have hc : stepCumulative w=fun i => (weightedControlCoefficient k w hw i:ℝ) := rfl
  unfold labelProfileValue
  rw [hend,hterm,hc]
  simp_rw [oneDim_profile_backward]
  simp only [diagonalMark_apply,profileGaussianRoot]
  rw [Jet3.heatLog_f]
  change (∫ x : EuclideanSpace ℝ (Fin 1),
    (finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
      (weightedControlCoefficient k w hw)).f (Real.sqrt (q 0:ℝ)*x 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))=heatLog (timeSpan 0 (q 0)) 0 _ 0
  rw [heatLog,ite_eq_left rfl]
  simpa only [hstart,zero_add] using oneDim_gaussian_average (timeSpan 0 (q 0))
    (finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
      (weightedControlCoefficient k w hw)).f 0

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

lemma quantileTrial_eq_integral (q : Time → Time) (hq : Measurable q) (t : Time) :
    quantileTrial q t=∫ u, (if q u ≤ t then (1:ℝ) else 0) ∂timeLaw := by
  change timeLaw.real {u | q u ≤ t}=∫ u, {u | q u ≤ t}.indicator (fun _ => (1:ℝ)) u ∂timeLaw
  rw [integral_indicator (measurableSet_le hq measurable_const),integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_QuantileControlContinuity
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

lemma cdfIndicator_integrable (a : Time) : Integrable (cdfIndicator a) timeLaw := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    ((measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const).aestronglyMeasurable)
  exact ae_of_all _ fun _ => by split_ifs <;> norm_num

lemma cdfIndicator_integral (a : Time) : (∫ t, cdfIndicator a t ∂timeLaw)=1-(a:ℝ) := by
  have he := timeTail_atom_integral a 0 1
  rw [show Ici (0:Time)=univ from Ici_bot,Measure.restrict_univ] at he
  change (∫ s, (if a ≤ s then (1:ℝ) else 0) ∂timeLaw)=1*(1-max (a:ℝ) 0) at he
  simpa only [cdfIndicator,one_mul,max_eq_left a.2.1] using he

lemma cdfIndicator_order {a b : Time} (hab : a≤b) (t : Time) : cdfIndicator b t ≤ cdfIndicator a t := by
  unfold cdfIndicator
  by_cases hb : b≤t
  · rw [ite_eq_left hb,ite_eq_left (hab.trans hb)]
  · rw [ite_eq_right hb]
    split_ifs <;> norm_num

lemma cdfIndicator_abs_integral (a b : Time) :
    (∫ t, |cdfIndicator a t-cdfIndicator b t| ∂timeLaw)=|(a:ℝ)-b| := by
  have hle {a b : Time} (hab : a≤b) :
      (∫ t, |cdfIndicator a t-cdfIndicator b t| ∂timeLaw)=(b:ℝ)-a := by
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (cdfIndicator_order hab _))]
    rw [integral_sub (cdfIndicator_integrable a) (cdfIndicator_integrable b),
      cdfIndicator_integral,cdfIndicator_integral]
    ring
  rcases le_total a b with hab | hba
  · rw [hle hab,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (a:ℝ)≤b from hab))]
  · simp_rw [abs_sub_comm (cdfIndicator a _) (cdfIndicator b _)]
    rw [hle hba,abs_of_nonneg (sub_nonneg.mpr (show (b:ℝ)≤a from hba))]

lemma quantileTrial_L1_le (q r : Time→Time) (hq : Measurable q) (hr : Measurable r) :
    (∫ t, |quantileTrial q t-quantileTrial r t| ∂timeLaw)≤
      ∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
  let F := fun p : Time×Time => |cdfIndicator (q p.2) p.1-cdfIndicator (r p.2) p.1|
  have hmq : Measurable (fun p : Time×Time => cdfIndicator (q p.2) p.1) :=
    measurable_const.ite (measurableSet_le (hq.comp measurable_snd) measurable_fst) measurable_const
  have hmr : Measurable (fun p : Time×Time => cdfIndicator (r p.2) p.1) :=
    measurable_const.ite (measurableSet_le (hr.comp measurable_snd) measurable_fst) measurable_const
  have hF : Integrable F (timeLaw.prod timeLaw) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) ((hmq.sub hmr).abs.aestronglyMeasurable)
    exact ae_of_all _ fun p => by dsimp [F,cdfIndicator]; split_ifs <;> norm_num
  have hpoint (t : Time) : |quantileTrial q t-quantileTrial r t|≤∫ u, F (t,u) ∂timeLaw := by
    rw [quantileTrial_eq_integral q hq,quantileTrial_eq_integral r hr]
    have hi (v : Time→Time) (hv : Measurable v) :
        Integrable (fun u => if v u≤t then (1:ℝ) else 0) timeLaw := by
      apply Integrable.mono' (integrable_const (1:ℝ))
        ((measurable_const.ite (measurableSet_le hv measurable_const) measurable_const).aestronglyMeasurable)
      exact ae_of_all _ fun _ => by split_ifs <;> norm_num
    rw [← integral_sub (hi q hq) (hi r hr)]
    simpa only [Real.norm_eq_abs,F,cdfIndicator] using (norm_integral_le_integral_norm
      (fun u : Time => (if q u≤t then (1:ℝ) else 0)-(if r u≤t then (1:ℝ) else 0)))
  calc
    _ ≤ ∫ t, ∫ u, F (t,u) ∂timeLaw ∂timeLaw :=
      integral_mono ((trial_integrable (quantileTrial q)).sub (trial_integrable (quantileTrial r))).abs
        hF.integral_prod_left hpoint
    _ = ∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
      rw [integral_integral_swap hF]
      exact integral_congr_ae (ae_of_all _ fun u => cdfIndicator_abs_integral (q u) (r u))

theorem controlValue_quantile_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (g : Jet3) (q r : Time→Time) (hq : Measurable q) (hr : Measurable r) :
    |controlValue P g.f (quantileTrial q)-controlValue P g.f (quantileTrial r)|≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*∫ u, |(q u:ℝ)-r u| ∂timeLaw := by
  apply (controlValue_trial_abs_sub_le P g.f _ _ ‖g.d1‖₊ g.lipschitz).trans
  exact mul_le_mul_of_nonneg_left (quantileTrial_L1_le q r hq hr) (by positivity)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileUpperTail
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma unit_valued_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {q : Time→Time} (hq : Measurable q) : Integrable (fun u => (q u:ℝ)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (measurable_subtype_coe.comp hq).aestronglyMeasurable
  exact ae_of_all _ fun u => by
    change ‖(q u:ℝ)‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (q u).property.1]
    exact (q u).property.2

lemma uniformQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileLower n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (show i.castSucc ≤ j.castSucc from hij))
lemma uniformQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileUpper n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (Fin.succ_le_succ_iff.mpr hij))
lemma sampleQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileLower n q) :=
  (uniformQuantileLower_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileUpper n q) :=
  (uniformQuantileUpper_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantile_bracket (n : ℕ) {q : Time→Time} (hq : Monotone q) (u : Time) :
    sampleQuantileLower n q u ≤ q u ∧ q u ≤ sampleQuantileUpper n q u :=
  ⟨hq (uniformQuantileCell_bounds n u).1,hq (uniformQuantileCell_bounds n u).2⟩

lemma sampleQuantile_gap_integral (n : ℕ) (q : Time→Time) :
    (∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw)=
      ((q 1:ℝ)-q 0)/(n+1:ℝ) := by
  change (∫ u, (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i)
    (uniformQuantileCell n u) ∂timeLaw)=_
  rw [uniformQuantileCell_integral n (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i),← Finset.mul_sum]
  unfold uniformQuantileUpper uniformQuantileLower
  rw [finite_sum_successive_differences (n+1) (fun i => (q (uniformQuantileGrid n i):ℝ)),
    uniformQuantileGrid_last,uniformQuantileGrid_zero]
  ring

lemma sampleQuantileLower_L1 (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    (∫ u, |(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw) ≤ 1/(n+1:ℝ) := by
  have hl := unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable
  have hu := unit_valued_integrable timeLaw (sampleQuantileUpper_mono n hq).measurable
  have hi := unit_valued_integrable timeLaw hq.measurable
  calc
    _  ≤  ∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw := by
      apply integral_mono (hl.sub hi).abs (hu.sub hl)
      intro u
      have hb := sampleQuantile_bracket n hq u
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonpos (sub_nonpos.mpr (show (sampleQuantileLower n q u:ℝ) ≤ q u from hb.1))]
      have ht : (q u:ℝ) ≤ sampleQuantileUpper n q u := hb.2
      linarith
    _ = ((q 1:ℝ)-q 0)/(n+1:ℝ) := sampleQuantile_gap_integral n q
    _  ≤  1/(n+1:ℝ) := div_le_div_of_nonneg_right (by have := (q 1).2.2; have := (q 0).2.1; linarith) (by positivity)

lemma sampleQuantileUpper_L1 (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    (∫ u, |(sampleQuantileUpper n q u:ℝ)-q u| ∂timeLaw) ≤ 1/(n+1:ℝ) := by
  have hl := unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable
  have hu := unit_valued_integrable timeLaw (sampleQuantileUpper_mono n hq).measurable
  have hi := unit_valued_integrable timeLaw hq.measurable
  calc
    _  ≤  ∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw := by
      apply integral_mono (hu.sub hi).abs (hu.sub hl)
      intro u
      have hb := sampleQuantile_bracket n hq u
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (show (q u:ℝ) ≤ sampleQuantileUpper n q u from hb.2))]
      exact sub_le_sub_left (show (sampleQuantileLower n q u:ℝ) ≤ q u from hb.1) _
    _ = ((q 1:ℝ)-q 0)/(n+1:ℝ) := sampleQuantile_gap_integral n q
    _  ≤  1/(n+1:ℝ) := div_le_div_of_nonneg_right (by have := (q 1).2.2; have := (q 0).2.1; linarith) (by positivity)

lemma sampleQuantile_trial (n : ℕ) (q : Fin (n+1)→Time) :
    quantileTrial (fun u => q (uniformQuantileCell n u))=
      weightedStepTrial (fun _ => 1/(n+1:ℝ)) q (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n) := by
  apply Trial.ext_fun
  intro t
  have hm : Measurable (fun u => q (uniformQuantileCell n u)) :=
    (measurable_of_finite q).comp (uniformQuantileCell_measurable n)
  rw [quantileTrial_eq_integral _ hm]
  rw [uniformQuantileCell_integral n (fun i => if q i ≤ t then (1:ℝ) else 0)]
  change (∑ i, (1/(n+1:ℝ))*(if q i ≤ t then (1:ℝ) else 0))=∑ i, if q i ≤ t then 1/(n+1:ℝ) else 0
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_QuantileControlTail
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

lemma sampleQuantile_control_error (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (g : Jet3) (q : Time→Time) (hq : Monotone q) (n : ℕ) :
    |controlValue P g.f (quantileTrial (sampleQuantileLower n q))-controlValue P g.f (quantileTrial q)| ≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ)) ∧
    |controlValue P g.f (quantileTrial (sampleQuantileUpper n q))-controlValue P g.f (quantileTrial q)| ≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ)) := by
  constructor
  · exact (controlValue_quantile_abs_sub_le P g _ _ (sampleQuantileLower_mono n hq).measurable hq.measurable).trans
      (mul_le_mul_of_nonneg_left (sampleQuantileLower_L1 n hq) (by positivity))
  · exact (controlValue_quantile_abs_sub_le P g _ _ (sampleQuantileUpper_mono n hq).measurable hq.measurable).trans
      (mul_le_mul_of_nonneg_left (sampleQuantileUpper_L1 n hq) (by positivity))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReference
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

lemma compactSpinGeometry_closed : IsClosed {Q : CompactArray CompactJointOverlap | CompactSpinGeometry Q} := by
  unfold CompactSpinGeometry
  simp only [ofPred_and,ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
        isClosed_le (by fun_prop) (by fun_prop)))

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

lemma unit_pow_abs_sub_le (a b : Time) (r : ℕ) :
    |(a:ℝ)^r-(b:ℝ)^r|≤(r:ℝ)*|(a:ℝ)-b| := by
  have hm : max |(a:ℝ)| |(b:ℝ)|≤1 := by
    rw [abs_of_nonneg a.prop.1,abs_of_nonneg b.prop.1]
    exact max_le a.prop.2 b.prop.2
  have hp : max |(a:ℝ)| |(b:ℝ)|^(r-1)≤1 := pow_le_one₀ (by positivity) hm
  calc
    _ ≤ |(a:ℝ)-b| *r*max |(a:ℝ)| |(b:ℝ)|^(r-1) := abs_pow_sub_pow_le ..
    _ ≤ |(a:ℝ)-b| *r*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

lemma unit_pow_integrable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (q : A→Time) (hq : Measurable q) (r : ℕ) : Integrable (fun u => (q u:ℝ)^r) μ := by
  apply Integrable.of_bound ((measurable_subtype_coe.comp hq).pow_const r).aestronglyMeasurable 1
  exact ae_of_all _ fun u => by
    change ‖(q u:ℝ)^r‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (q u).prop.1 r)]
    exact pow_le_one₀ (q u).prop.1 (q u).prop.2

lemma sampleQuantileLower_moment_tendsto (q : Time→Time) (hq : Monotone q) (r : ℕ) :
    Tendsto (fun n => ∫ u, (sampleQuantileLower n q u:ℝ)^r ∂timeLaw) atTop
      (𝓝 (∫ u, (q u:ℝ)^r ∂timeLaw)) := by
  have hz : Tendsto (fun n : ℕ => (r:ℝ)*(1/(n+1:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (r:ℝ)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
  rw [Real.dist_eq,←integral_sub (unit_pow_integrable timeLaw _ (sampleQuantileLower_mono n hq).measurable r)
    (unit_pow_integrable timeLaw q hq.measurable r)]
  calc
    _ ≤ ∫ u, |(sampleQuantileLower n q u:ℝ)^r-(q u:ℝ)^r| ∂timeLaw := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (fun u => (sampleQuantileLower n q u:ℝ)^r-(q u:ℝ)^r))
    _ ≤ ∫ u, (r:ℝ)*|(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw := by
      apply integral_mono
        ((unit_pow_integrable timeLaw _ (sampleQuantileLower_mono n hq).measurable r).sub
          (unit_pow_integrable timeLaw q hq.measurable r)).abs
        (((unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable).sub
          (unit_valued_integrable timeLaw hq.measurable)).abs.const_mul (r:ℝ))
      exact fun u => unit_pow_abs_sub_le _ _ r
    _ = (r:ℝ)*∫ u, |(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw := integral_const_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (sampleQuantileLower_L1 n hq) (by positivity)

lemma quantileSpinLaw_integral (q : Time→Time) (hq : Measurable q)
    (F : CompactOverlap→ℝ) (hF : Measurable F) :
    (∫ x, F x ∂(quantileSpinLaw q hq : Measure CompactOverlap))=∫ u, F (timeSpin (q u)) ∂timeLaw :=
  integral_map (timeSpin_continuous.measurable.comp hq).aemeasurable hF.aestronglyMeasurable

theorem quantile_reference_exists (q : Time→Time) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (FreshPartitionRange g.f)),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
        ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _)) ∧
      (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
        controlValue P g.f (quantileTrial q) := by
  have hex (n : ℕ) := labelProfile_reference_full_exists n (fun _=>1/(n+1:ℝ))
    (by intro i; positivity) (uniformQuantileWeights_sum n) (uniformQuantileLower n q)
    (uniformQuantileLower_mono n hq) g
  choose μ ξ hGG hgeo hpair hm hl using hex
  obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence μ
  have hG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0 := by
    intro r i G a
    apply compactGGDefect_limit hlim r i G a
    simp only [Function.comp_apply,hGG]
    exact tendsto_const_nhds
  have hgeom : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q := by
    apply (mem_ae_iff_prob_eq_one compactSpinGeometry_closed.measurableSet).mpr
    have hv := weak_limit_closed_full hlim compactSpinGeometry_closed (fun n => ?_)
    · simp only [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]
    · have hh := (mem_ae_iff_prob_eq_one compactSpinGeometry_closed.measurableSet).mp (hgeo (s n))
      rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
      exact ENNReal.coe_injective hh
  have hp : (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
      (quantileSpinLaw q hq.measurable : Measure CompactOverlap) := by
    let ρ : ProbabilityMeasure CompactOverlap := ⟨(ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1),
      (Measure.isProbabilityMeasure_map_iff (show Measurable
        (fun array : CompactArray CompactJointOverlap => (array 0 1).1)
        from by fun_prop).aemeasurable).2 inferInstance⟩
    have he : ρ=quantileSpinLaw q hq.measurable := by
      apply probability_Icc_eq_of_moments
      intro r
      rw [quantileSpinLaw_integral q hq.measurable (fun x => x.val^r) (by fun_prop)]
      change (∫ x : CompactOverlap, x.val^r ∂(ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))=_
      rw [integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable (show Measurable (fun x : CompactOverlap => x.val^r) from by fun_prop).aestronglyMeasurable]
      let F : CompactOverlap→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x=>x.val^r,by fun_prop⟩
      let FF : CompactArray CompactJointOverlap→ᵇℝ := F.compContinuous ⟨fun Q => (Q 0 1).1,by fun_prop⟩
      have hν := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction FF).continuousAt.tendsto.comp hlim
      have hv n : (∫ Q, FF Q ∂(μ n : Measure _))=∫ u, (sampleQuantileLower n q u:ℝ)^r ∂timeLaw := by
        change (∫ Q, F (Q 0 1).1 ∂(μ n : Measure (CompactArray CompactJointOverlap)))=_
        rw [hpair n F]
        exact (uniformQuantileCell_integral n (fun i => (uniformQuantileLower n q i:ℝ)^r)).symm
      change Tendsto (fun n => ∫ Q, FF Q ∂(μ (s n) : Measure (CompactArray CompactJointOverlap))) atTop
        (𝓝 (∫ Q, FF Q ∂(ν : Measure (CompactArray CompactJointOverlap)))) at hν
      simp_rw [hv] at hν
      exact tendsto_nhds_unique hν ((sampleQuantileLower_moment_tendsto q hq r).comp hs.tendsto_atTop)
    exact congrArg (fun x : ProbabilityMeasure CompactOverlap => (x : Measure CompactOverlap)) he
  have hmom r : Tendsto (fun n => ∫ x, x.val^r ∂(ξ (s n) : Measure (FreshPartitionRange g.f))) atTop
      (𝓝 (∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _))) := by
    simp_rw [hm]
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (freshReplicaArrayKernel (expBCF 1 g.f) r)).continuousAt.tendsto.comp hlim
  obtain ⟨η,hη,hηm⟩ := compact_moment_limit (fun n=>ξ (s n)) _ hmom
  refine ⟨ν,η,hG,hgeom,hp,hηm,?_⟩
  have hlog : Continuous (fun x : FreshPartitionRange g.f => Real.log x.val) :=
    continuous_subtype_val.log fun x => ne_of_gt ((Real.exp_pos _).trans_le x.prop.1)
  let F : FreshPartitionRange g.f→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨_,hlog⟩
  have hv := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hη
  have he n : (∫ x, F x ∂(ξ n : Measure (FreshPartitionRange g.f)))=
      controlValue P g.f (quantileTrial (sampleQuantileLower n q)) := by
    change (∫ x, Real.log x.val ∂(ξ n : Measure (FreshPartitionRange g.f)))=_
    rw [hl n,labelProfileValue_control n _ _ (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n)
      (uniformQuantileLower_mono n hq) g P hB]
    exact congrArg (controlValue P g.f) (sampleQuantile_trial n (uniformQuantileLower n q)).symm
  change Tendsto (fun n => ∫ x, F x ∂(ξ (s n) : Measure (FreshPartitionRange g.f))) atTop
    (𝓝 (∫ x, F x ∂(η : Measure (FreshPartitionRange g.f)))) at hv
  simp_rw [he] at hv
  have hc : Tendsto (fun n => controlValue P g.f (quantileTrial (sampleQuantileLower n q))) atTop
      (𝓝 (controlValue P g.f (quantileTrial q))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      (show Tendsto (fun n : ℕ => (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ))) atTop (𝓝 0) from by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul ((3/2:ℝ)*(‖g.d1‖₊:ℝ)^2))
    exact (sampleQuantile_control_error P g q hq n).1
  exact tendsto_nhds_unique hv (hc.comp hs.tendsto_atTop)

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

theorem compactGG_freshLog_control_oai (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0)
    (hgeo : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (g : Jet3) (η : ProbabilityMeasure (FreshPartitionRange g.f))
    (hm : ∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
      ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _))
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
      controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) := by
  obtain ⟨ρ,ξ,hG,hge,hp,hξ,hl⟩ := quantile_reference_exists
    (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst)) (boundedQuantile_monotone _) g P hB
  rw [freshLog_eq_of_pair_law ν ρ hGG hG hgeo hge
    ((compactPositivePairLaw_spin_quantile ν hn).trans hp.symm) g.f η ξ hm hξ]
  exact hl

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control_oai := @OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control_oai
