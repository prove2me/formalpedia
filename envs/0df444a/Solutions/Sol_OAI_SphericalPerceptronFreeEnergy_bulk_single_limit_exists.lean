-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:31:41.091685+00:00
-- url     : https://prove2.me/submissions/0f4715a6-a5ce-418f-870b-5b7126a1d090

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceLabelSingle_witness
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_array_limit_label_law
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_contact_monomial_tendsto
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_perturbation_contact_exists

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CountableGaussianField
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

variable {S : Type*}

lemma sum_range_cutoff (a : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range n, if i < m then a i else 0)=∑ i ∈ Finset.range (min n m), a i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      by_cases h : n < m
      · have hn : min n m=n := min_eq_left (by omega)
        have hn' : min (n+1) m=n+1 := min_eq_left (by omega)
        rw [hn,hn',ite_eq_left h,Finset.sum_range_succ]
      · have hn : min n m=m := min_eq_right (by omega)
        have hn' : min (n+1) m=m := min_eq_right (by omega)
        rw [hn,hn',ite_eq_right h,add_zero]

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

end Tilt

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

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptronFreeEnergy.heatLog]
  · rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_DecoratedWeightedTotal
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

lemma fractionalLogMoment_centered {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b : ℝ} (hb : b ≠ 0) {f : X×S → ℝ} (x : X)
    (hI : Integrable (fun s => Real.exp (b*f (x,s))) ν) :
    Integrable (fun s => Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x))) ν ∧
    (∫ s, Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) ∂ν) = 1 := by
  have hp : 0 < ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    apply integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hI |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hfac (s : S) : Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) =
      Real.exp (-(Real.log (∫ t, Real.exp (b*f (x,t)) ∂ν)))*Real.exp (b*f (x,s)) := by
    rw [← Real.exp_add]
    congr 1
    unfold fractionalLogMoment
    field_simp
    ring
  constructor
  · simp_rw [hfac]
    exact hI.const_mul _
  · simp_rw [hfac]
    rw [integral_const_mul,Real.exp_neg,Real.exp_log hp,inv_mul_cancel₀ hp.ne']

lemma finiteCascadeShifts_normalized_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, z i ≠ 0) (H : X → ℝ)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) : ∀ i x,
    Integrable (fun s => Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s))) ν ∧
    (∫ s, Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s)) ∂ν) = 1 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    rcases hI with ⟨hroot,htail⟩
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) (fun k => hz k.succ) htail j) i
    intro x
    exact fractionalLogMoment_centered ν (hz 0)
      (f := fun p => finiteCascadeLogRecursion ν step n (fun j => z j.succ) H (step p)) x (hroot x)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedVertices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedLeafVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafVertex n l) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [indexedLeafVertex] at hij
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [indexedLeafVertex] at hij
      | succ j =>
        simpa only [Fin.succ_inj] using ih l.2.2 (by simpa [indexedLeafVertex] using hij)

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
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapBlock
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

lemma gg_star_growth_impossible {a : ℕ → ℝ} {N ζ : ℝ}
    (hN : 2 ≤ N) (hζ : 0 < ζ) (ha : ∀ k, 0 ≤ a k) (hzero : 0 < a 0)
    (hrec : ∀ k, (N + k) * a (k + 1) = (N + k - 1 + ζ) * a k)
    (hbound : ∀ k : ℕ, (k + 1 : ℝ) * a k ≤ 1) : False := by
  let b : ℕ → ℝ := fun k => (N + k - 1) * a k
  have hbzero : 0 < b 0 := by dsimp [b]; nlinarith
  have hdiff (k : ℕ) : b (k + 1) = b k + ζ * a k := by
    dsimp [b]
    push_cast
    nlinarith [hrec k]
  have hbmono : Monotone b := monotone_nat_of_le_succ fun k => by
    rw [hdiff]
    exact le_add_of_nonneg_right (mul_nonneg hζ.le (ha k))
  have hblower (k : ℕ) : b 0 ≤ b k := hbmono (Nat.zero_le k)
  have hbupper (k : ℕ) : b k ≤ N := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc
      b k ≤ N * ((k + 1 : ℝ) * a k) := by
        dsimp [b]
        have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
      _ ≤ N := by nlinarith [hbound k]
  have hsum (k : ℕ) : ζ * ∑ j ∈ Finset.range k, a j = b k - b 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, mul_add, ih, hdiff]; ring
  have hasum : Summable a := by
    apply summable_of_sum_range_le ha (c := N / ζ)
    intro k
    apply (le_div_iff₀ hζ).mpr
    nlinarith [hsum k, hbupper k]
  have hdom (k : ℕ) : (1 / (k + 1 : ℝ)) ≤ (N / b 0) * a k := by
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [div_le_iff₀ hk]
    have : b 0 ≤ N * ((k + 1 : ℝ) * a k) := by
      calc b 0 ≤ b k := hblower k
           _ ≤ N * ((k + 1 : ℝ) * a k) := by
             dsimp [b]
             have hknonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
             have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
             nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
    have hn : N * ((k + 1 : ℝ) * a k) / b 0 ≥ 1 :=
      (le_div_iff₀ hbzero).mpr (by simpa using this)
    calc 1 ≤ N * ((k + 1 : ℝ) * a k) / b 0 := hn
         _ = (N / b 0) * a k * (k + 1 : ℝ) := by ring
  have hharm : Summable (fun k : ℕ => 1 / (k + 1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hdom (hasum.mul_left (N / b 0))
  have hharm' : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hharm
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hharm')

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapArray
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

lemma copyBlock_measurable (r j : ℕ) : Measurable (copyBlock r j) := by
  exact Measurable.of_eval fun firstIndex => Measurable.of_eval fun secondIndex =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma copyEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (j : ℕ) : MeasurableSet (copyEvent r s j) :=
  hs.preimage (copyBlock_measurable r j)

lemma copyIndex_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (i : Fin (r + 1)) :
    π (copyIndex r j i) = copyIndex r (π j) i := by
  by_cases hi : i.val = r
  · simp [copyIndex, hi]
  · simp only [copyIndex, ite_eq_right hi]
    exact hπ i (by omega)

lemma copyBlock_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (Q : OverlapArray) :
    copyBlock r j (relabelArray π Q) = copyBlock r (π j) Q := by
  ext a b
  simp only [copyBlock, relabelArray, copyIndex_relabel r j π hπ]

lemma copyEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (s : Set (OverlapBlock (r + 1))) :
    relabelArray π ⁻¹' copyEvent r s j = copyEvent r s (π j) := by
  ext Q
  simp only [copyEvent, mem_preimage, copyBlock_relabel r j π hπ]

lemma uniqueEvent_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    MeasurableSet (uniqueEvent A i) := by
  simp only [uniqueEvent, ofPred_and, ofPred_forall]
  exact (hA i).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)

lemma uniqueEvent_disjoint {Ω ι : Type*} (A : ι → Set Ω) :
    Pairwise (fun i j => Disjoint (uniqueEvent A i) (uniqueEvent A j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hi.2 j hij.symm hj.1

lemma uniqueEvent_probability_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (i₀ : ι)
    (hsame : ∀ i, μ.real (uniqueEvent A i) = μ.real (uniqueEvent A i₀)) :
    Fintype.card ι * μ.real (uniqueEvent A i₀) ≤ 1 := by
  have h := sum_measureReal_le_measureReal_univ (μ := μ) (s := Finset.univ)
    (t := uniqueEvent A) (fun i _ => uniqueEvent_measurable A hA i)
    (fun i _ j _ hij => uniqueEvent_disjoint A hij)
  simp only [hsame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simpa [Measure.real] using h

lemma uniqueEvent_preimage {Ω ι : Type*} {f : Ω → Ω} (A : ι → Set Ω)
    (e : Equiv.Perm ι) (h : ∀ j, f ⁻¹' A j = A (e j)) (i : ι) :
    f ⁻¹' uniqueEvent A i = uniqueEvent A (e i) := by
  ext ω
  have hm (j : ι) : f ω ∈ A j ↔ ω ∈ A (e j) := by
    change ω ∈ f ⁻¹' A j ↔ ω ∈ A (e j)
    rw [h]
  constructor
  · intro hw
    refine ⟨(hm i).mp hw.1, ?_⟩
    intro j hji hj
    apply hw.2 (e.symm j) (fun heq => hji (by rw [← e.apply_symm_apply j, heq]))
    exact (hm _).mpr (by simpa using hj)
  · intro hw
    refine ⟨(hm i).mpr hw.1, ?_⟩
    intro j hji hj
    exact hw.2 (e j) (fun h' => hji (e.injective h')) ((hm j).mp hj)

lemma uniqueCopy_probability_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r k : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) :
    (k + 1 : ℝ) * μ.real (uniqueEvent
      (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) ≤ 1 := by
  let A : Fin (k + 1) → Set OverlapArray := fun j => copyEvent r s (r + j)
  have hA (j) : MeasurableSet (A j) := copyEvent_measurable r hs _
  have hsame (i : Fin (k + 1)) : μ.real (uniqueEvent A i) = μ.real (uniqueEvent A 0) := by
    let e : Equiv.Perm (Fin (k + 1)) := Equiv.swap i 0
    let π : Equiv.Perm ℕ := Equiv.swap (r + i) (r + (0 : Fin (k + 1)))
    have hfix : ∀ a < r, π a = a := by
      intro a ha
      exact Equiv.swap_apply_of_ne_of_ne (by omega) (by simp; omega)
    have hinj : Function.Injective (fun j : Fin (k + 1) => r + j.val) := by
      intro a b hab
      apply Fin.ext
      exact Nat.add_left_cancel hab
    have hmap (j : Fin (k + 1)) : relabelArray π ⁻¹' A j = A (e j) := by
      dsimp [A]
      rw [copyEvent_relabel r _ π hfix]
      congr 1
      exact (hinj.map_swap i 0 j).symm
    have he : e 0 = i := Equiv.swap_apply_right _ _
    rw [← he, ← uniqueEvent_preimage A e hmap]
    exact (hEx _ _).measureReal_preimage (uniqueEvent_measurable A hA 0).nullMeasurableSet
  have h := uniqueEvent_probability_bound μ A hA 0 hsame
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using h

lemma prefixBlock_measurable {n m : ℕ} (h : n ≤ m) : Measurable (prefixBlock h) := by
  exact Measurable.of_eval fun firstIndex => Measurable.of_eval fun secondIndex =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma starMatrices_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (k : ℕ) : MeasurableSet (starMatrices r s t k) := by
  simp only [starMatrices, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter (hs.preimage (prefixBlock_measurable _))
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply _)) measurable_const

lemma starEvent_preimage (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    overlapBlock id (r + 1 + k) ⁻¹' starMatrices r s t k = starEvent r s t k := by
  ext Q
  have hprefix : prefixBlock (Nat.le_add_right (r + 1) k)
      (overlapBlock id (r + 1 + k) Q) = copyBlock r r Q := by
    ext a b
    simp [prefixBlock, overlapBlock, copyBlock]
  simp only [mem_preimage, starMatrices, mem_ofPred_eq, hprefix, starEvent,
    copyEvent, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hj hne => h' ⟨j, hj⟩ hne⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hne => h' j j.isLt hne⟩

lemma starEvent_succ (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    starEvent r s t (k + 1) =
      starEvent r s t k ∩ {Q | Q r (r + 1 + k) < t} := by
  ext Q
  constructor
  · rintro ⟨hA, hQ⟩
    exact ⟨⟨hA, fun j hj hne => hQ j (by omega) hne⟩,
      hQ (r + 1 + k) (by omega) (by omega)⟩
  · rintro ⟨⟨hA, hQ⟩, hn⟩
    refine ⟨hA, ?_⟩
    intro j hj hne
    by_cases hlt : j < r + 1 + k
    · exact hQ j hlt hne
    · have heq : j = r + 1 + k := by omega
      simpa only [mem_ofPred_eq, heq] using hn

lemma starEvent_zero (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ)
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    starEvent r s t 0 = copyEvent r s r := by
  ext Q
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun j hj hne => hrow Q h j (by omega)⟩

lemma gg_star_recurrence (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hGG : GhirlandaGuerra μ id) {r : ℕ} (hr : 1 ≤ r)
    {s : Set (OverlapBlock (r + 1))} (hs : MeasurableSet s) (t : ℝ) (k : ℕ) :
    ((r + 1 + k : ℕ) : ℝ) * μ.real (starEvent r s t (k + 1)) =
      (((r + 1 + k : ℕ) : ℝ) - 1 + μ.real {Q | Q 0 1 < t}) *
        μ.real (starEvent r s t k) := by
  classical
  let m := r + 1 + k
  let i : Fin m := ⟨r, by dsimp [m]; omega⟩
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := hGG m hm i (starMatrices r s t k) (starMatrices_measurable r hs t k)
    (Iio t) measurableSet_Iio
  rw [starEvent_preimage] at h
  change μ.real (starEvent r s t k ∩ {Q | Q r m < t}) =
    μ.real (starEvent r s t k) * μ.real {Q | Q 0 1 < t} / m +
    (∑ j ∈ Finset.univ.erase i,
      μ.real (starEvent r s t k ∩ {Q | Q r j < t})) / m at h
  have hpair (j : Fin m) (hne : j ≠ i) :
      starEvent r s t k ∩ {Q | Q r j < t} = starEvent r s t k := by
    apply inter_eq_left.mpr
    intro Q hQ
    exact hQ.2 j j.isLt (fun heq => hne (Fin.ext heq))
  rw [Finset.sum_congr rfl (fun j hj => congrArg μ.real
    (hpair j (Finset.ne_of_mem_erase hj)))] at h
  have hcard : ((Finset.univ.erase i).card : ℝ) = (m : ℝ) - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega)]
    norm_num
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
  rw [← starEvent_succ] at h
  have hmul := congrArg (fun x : ℝ => (m : ℝ) * x) h
  field_simp at hmul
  dsimp [m] at hmul
  nlinarith [hmul]

lemma duplicateEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (j : ℕ) : MeasurableSet (duplicateEvent r s t j) :=
  ((copyEvent_measurable r hs r).inter (copyEvent_measurable r hs j)).inter
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply r)) measurable_const)

lemma duplicateEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (hr : π r = r)
    (s : Set (OverlapBlock (r + 1))) (t : ℝ) :
    relabelArray π ⁻¹' duplicateEvent r s t j = duplicateEvent r s t (π j) := by
  ext Q
  simp only [duplicateEvent, copyEvent, mem_preimage, mem_inter_iff, mem_ofPred_eq,
    copyBlock_relabel r r π hπ, copyBlock_relabel r j π hπ, hr, relabelArray]

lemma duplicateEvent_null_future (μ : Measure OverlapArray)
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) {j : ℕ} (hj : r + 1 ≤ j) :
    μ (duplicateEvent r s t j) = 0 := by
  let π : Equiv.Perm ℕ := Equiv.swap (r + 1) j
  have hfix : ∀ a ≤ r, π a = a := by
    intro a ha
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  calc
    μ (duplicateEvent r s t j) = μ (relabelArray π ⁻¹' duplicateEvent r s t (r + 1)) := by
      rw [duplicateEvent_relabel r (r + 1) π (fun a ha => hfix a ha.le) (hfix r le_rfl)]
      simp only [π, Equiv.swap_apply_left]
    _ = μ (duplicateEvent r s t (r + 1)) :=
      (hEx _ _).measure_preimage (duplicateEvent_measurable r hs t (r + 1)).nullMeasurableSet
    _ = 0 := hzero

lemma star_unique_bound_of_no_duplication (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) (k : ℕ) :
    (k + 1 : ℝ) * μ.real (starEvent r s t k) ≤ 1 := by
  have hnul (j : Fin (k + 1)) : ∀ᵐ Q ∂μ, j ≠ 0 → Q ∉ duplicateEvent r s t (r + j) := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hz : μ (duplicateEvent r s t (r + j)) = 0 :=
        duplicateEvent_null_future μ hEx r hs t hzero (by
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with Q hQ
      exact fun _ => hQ
  have hae : starEvent r s t k ≤ᵐ[μ]
      uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0 := by
    filter_upwards [ae_all_iff.mpr hnul] with Q hQ
    intro hstar
    refine ⟨by simpa using hstar.1, ?_⟩
    intro j hj hmem
    apply hQ j hj
    refine ⟨⟨hstar.1, hmem⟩, ?_⟩
    exact hstar.2 (r + j) (by have := j.isLt; omega) (by
      have : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega)
  have hle : μ.real (starEvent r s t k) ≤ μ.real
      (uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans
    (uniqueCopy_probability_bound μ hEx r k hs)

lemma edge_probability_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    (a b i j : ℕ) (t : ℝ) :
    μ.real {Q | Q (Equiv.swap a b i) (Equiv.swap a b j) < t} =
      μ.real {Q | Q i j < t} := by
  exact (hEx a b).measureReal_preimage
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply i))
      measurable_const).nullMeasurableSet

theorem gg_duplicate_last (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (copyEvent r s r))
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    0 < μ.real (duplicateEvent r s t (r + 1)) := by
  by_contra hbad
  have hz : μ (duplicateEvent r s t (r + 1)) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (le_antisymm (not_lt.mp hbad) (measureReal_nonneg))
  have heq : μ.real {Q | Q r 0 < t} = μ.real {Q | Q 0 1 < t} := by
    have h₁ := edge_probability_swap μ hEx 1 r 1 0 t
    have h₂ := edge_probability_swap μ hEx 0 1 0 1 t
    have hr0 : (0 : ℕ) ≠ r := by omega
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : ℕ) ≠ 1) hr0] at h₁ h₂
    exact h₁.trans h₂
  have hζ : 0 < μ.real {Q | Q 0 1 < t} := by
    rw [← heq]
    refine hA.trans_le (measureReal_mono ?_)
    exact fun Q hQ => hrow Q hQ 0 (by omega)
  apply gg_star_growth_impossible (a := fun k => μ.real (starEvent r s t k))
    (N := (r + 1 : ℕ)) (ζ := μ.real {Q | Q 0 1 < t})
    (by exact_mod_cast (by omega : 2 ≤ r + 1)) hζ (fun _ => measureReal_nonneg)
  · rwa [starEvent_zero r s t hrow]
  · intro k
    simpa only [Nat.cast_add] using gg_star_recurrence μ hGG hr hs t k
  · exact star_unique_bound_of_no_duplication μ hEx r hs t hz

lemma relabelBlock_measurable {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Measurable (relabelBlock e) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma fin_swap_val {n : ℕ} (p q a : Fin n) :
    (Equiv.swap p q a).val = Equiv.swap p.val q.val a.val :=
  Fin.val_injective.map_swap p q a

lemma relabelBlock_swap {n : ℕ} (p q : Fin n) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q) (overlapBlock id n Q) =
      overlapBlock id n (relabelArray (Equiv.swap p.val q.val) Q) := by
  ext a b
  simp only [relabelBlock, overlapBlock, id_eq, relabelArray, fin_swap_val]

lemma relabelArray_swap_swap (p q : ℕ) (Q : OverlapArray) :
    relabelArray (Equiv.swap p q) (relabelArray (Equiv.swap p q) Q) = Q := by
  ext a b
  simp [relabelArray]

lemma replaceBlock_last (r j : ℕ) (Q : OverlapArray) :
    replaceBlock (Fin.last r) j Q = copyBlock r j Q := by
  have h (a : Fin (r + 1)) : replaceIndex (Fin.last r) j a = copyIndex r j a := by
    simp [replaceIndex, copyIndex, Fin.ext_iff]
  ext a b
  simp only [replaceBlock, copyBlock, h]

lemma replaceBlock_swap {n : ℕ} (p q : Fin n) {j : ℕ} (hj : n ≤ j) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q)
      (replaceBlock q j (relabelArray (Equiv.swap p.val q.val) Q)) =
        replaceBlock p j Q := by
  have h (a : Fin n) : Equiv.swap p.val q.val (replaceIndex q j (Equiv.swap p q a)) =
      replaceIndex p j a := by
    by_cases ha : a = p
    · subst a
      simp only [Equiv.swap_apply_left, replaceIndex, ↓reduceIte]
      exact Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by have := q.isLt; omega)
    · have he : Equiv.swap p q a ≠ q := by
        intro h
        apply ha
        have := congrArg (Equiv.swap p q) h
        simpa using this
      simp only [replaceIndex, ite_eq_right he, ite_eq_right ha, fin_swap_val,
        Equiv.swap_apply_self]
  ext a b
  exact congrArg₂ Q (h a) (h b)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PatternMatrices
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

lemma block_event_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    {n : ℕ} (p q : Fin n) {s : Set (OverlapBlock n)} (hs : MeasurableSet s) :
    μ.real (overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s)) =
      μ.real (overlapBlock id n ⁻¹' s) := by
  have heq : overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s) =
      relabelArray (Equiv.swap p.val q.val) ⁻¹' (overlapBlock id n ⁻¹' s) := by
    ext Q
    change relabelBlock (Equiv.swap p q) (overlapBlock id n Q) ∈ s ↔ _
    rw [relabelBlock_swap]
    rfl
  rw [heq]
  exact (hEx _ _).measureReal_preimage
    (hs.preimage (Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _))).nullMeasurableSet

theorem gg_duplicate_index (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) (p : Fin (r + 1)) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' s))
    (hrow : ∀ Q ∈ overlapBlock id (r + 1) ⁻¹' s,
      ∀ j : Fin (r + 1), j ≠ p → Q p j < t) :
    0 < μ.real ((overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
      {Q | Q p (r + 1) < t}) := by
  let q : Fin (r + 1) := Fin.last r
  let e := Equiv.swap p q
  let π := Equiv.swap p.val q.val
  let s' := relabelBlock e ⁻¹' s
  have hs' : MeasurableSet s' := hs.preimage (relabelBlock_measurable e)
  have hbase : copyEvent r s' r = overlapBlock id (r + 1) ⁻¹' s' := by
    ext Q
    change copyBlock r r Q ∈ s' ↔ overlapBlock id (r + 1) Q ∈ s'
    have hb : copyBlock r r Q = overlapBlock id (r + 1) Q := by
      ext a b
      simp [copyBlock, overlapBlock]
    rw [hb]
  have hA' : 0 < μ.real (copyEvent r s' r) := by
    rw [hbase]
    exact (block_event_swap μ hEx p q hs).symm ▸ hA
  have hrow' : ∀ Q ∈ copyEvent r s' r, ∀ j < r, Q r j < t := by
    intro Q hQ j hj
    have hmem : relabelArray π Q ∈ overlapBlock id (r + 1) ⁻¹' s := by
      rw [hbase] at hQ
      change relabelBlock e (overlapBlock id (r + 1) Q) ∈ s at hQ
      rwa [relabelBlock_swap] at hQ
    let a : Fin (r + 1) := ⟨j, by omega⟩
    have hne : e a ≠ p := by
      intro h
      have h' := congrArg e h
      have haq : a = q := by simpa [e] using h'
      have := congrArg Fin.val haq
      dsimp [a, q] at this
      omega
    have h := hrow (relabelArray π Q) hmem (e a) hne
    have hp : π p.val = r := by simp [π, q]
    have ha : π (e a).val = j := by simp [π, e, fin_swap_val, a]
    simpa only [relabelArray, hp, ha] using h
  have hD := gg_duplicate_last μ hEx hGG hr hs' t hA' hrow'
  have hset : relabelArray π ⁻¹' duplicateEvent r s' t (r + 1) =
      (overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
        {Q | Q p (r + 1) < t} := by
    ext Q
    have hfirst : copyBlock r r (relabelArray π Q) ∈ s' ↔
        overlapBlock id (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r r (relabelArray π Q)) ∈ s ↔ _
      have hb : copyBlock r r (relabelArray π Q) =
          overlapBlock id (r + 1) (relabelArray π Q) := by
        ext a b
        simp [copyBlock, overlapBlock]
      rw [hb, relabelBlock_swap, relabelArray_swap_swap]
    have hsecond : copyBlock r (r + 1) (relabelArray π Q) ∈ s' ↔
        replaceBlock p (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r (r + 1) (relabelArray π Q)) ∈ s ↔ _
      rw [← replaceBlock_last]
      change relabelBlock (Equiv.swap p q)
        (replaceBlock q (r + 1) (relabelArray (Equiv.swap p.val q.val) Q)) ∈ s ↔ _
      rw [replaceBlock_swap p q (le_refl _)]
    have hp : π r = p.val := by exact Equiv.swap_apply_right _ _
    have hnew : π (r + 1) = r + 1 :=
      Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by dsimp [q]; omega)
    change ((copyBlock r r (relabelArray π Q) ∈ s' ∧
      copyBlock r (r + 1) (relabelArray π Q) ∈ s') ∧
      Q (π r) (π (r + 1)) < t) ↔ ((overlapBlock id (r + 1) Q ∈ s ∧
        replaceBlock p (r + 1) Q ∈ s) ∧ Q p (r + 1) < t)
    rw [hfirst, hsecond, hp, hnew]
  rw [← hset]
  rwa [(hEx _ _).measureReal_preimage
    (duplicateEvent_measurable r hs' t (r + 1)).nullMeasurableSet]

lemma patternMatrices_measurable {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) :
    MeasurableSet (patternMatrices labels C) := by
  simp only [patternMatrices, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (hC _ _).preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))

lemma pattern_append_of_duplicate {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (p : Fin n) (t : ℝ) (hdiag : C (labels p) (labels p) = Iio t)
    (Q : OverlapArray) (hSym : ∀ i j, Q i j = Q j i)
    (hA : overlapBlock id n Q ∈ patternMatrices labels C)
    (hB : replaceBlock p n Q ∈ patternMatrices labels C) (hedge : Q p n < t) :
    overlapBlock id (n + 1) Q ∈ patternMatrices (appendLabel labels (labels p)) C := by
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro j
    refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) j
    by_cases hb : b = p
    · subst b
      simpa [overlapBlock, hdiag, hSym n p] using hedge
    · have h := hB p b (Ne.symm hb)
      simpa [replaceBlock, replaceIndex, hb, overlapBlock] using h
  · intro j
    refine Fin.lastCases (fun _ => ?_) (fun b hab => ?_) j
    · by_cases ha : a = p
      · subst a
        simpa [overlapBlock, hdiag] using hedge
      · have h := hB a p ha
        simpa [replaceBlock, replaceIndex, ha, overlapBlock] using h
    · have h := hA a b (fun h => hab (congrArg Fin.castSucc h))
      simpa [overlapBlock] using h

theorem gg_pattern_append (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {r : ℕ} (hr : 1 ≤ r) (labels : Fin (r + 1) → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin (r + 1)) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (r + 1 + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  have hd := gg_duplicate_index μ hEx hGG hr p (patternMatrices_measurable labels C hC) t hA
    (fun Q hQ j hj => hcut _ _ (hQ p j (Ne.symm hj)))
  apply hd.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hSym] with Q hQ
  exact fun h => pattern_append_of_duplicate labels C p t hdiag Q hQ h.1.1 h.1.2 h.2

lemma gg_pattern_append_nat (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {n : ℕ} (hn : 2 ≤ n) (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin n) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (n + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  cases n with
  | zero => omega
  | succ r => exact gg_pattern_append μ hEx hGG hSym (by omega) labels C hC p t hdiag hcut hA

lemma appendLabel_tripleLabels {n : ℕ} (hn : 3 ≤ n) :
    appendLabel (tripleLabels n) (tripleLabels n ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩) =
      tripleLabels (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · apply Fin.ext
    simp [tripleLabels]
  · simp [tripleLabels]

theorem gg_triple_pattern (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (C : Fin 3 → Fin 3 → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (t : ℝ)
    (hdiag : ∀ k, C k k = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) C)) :
    ∀ n ≥ 3, 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices (tripleLabels n) C) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hA
  | succ n hn ih =>
    have h := gg_pattern_append_nat μ hEx hGG hSym (by omega) (tripleLabels n) C hC
      ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩ t (hdiag _) hcut ih
    rwa [appendLabel_tripleLabels hn] at h

open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma inner_replicaMean {n : ℕ} (v w : Fin n → H) :
    ⟪replicaMean v, replicaMean w⟫_ℝ =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ⟪v i, w j⟫_ℝ := by
  simp only [replicaMean, real_inner_smul_left, real_inner_smul_right]
  rw [sum_inner]
  simp_rw [inner_sum]
  ring

lemma replicaMean_norm_sq_le {n : ℕ} (hn : 0 < n) (v : Fin n → H) {c : ℝ}
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ c) :
    ‖replicaMean v‖ ^ 2 ≤ c + (1 - c) / n := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow (i : Fin n) : (∑ j, ⟪v i, v j⟫_ℝ) ≤ 1 + ((n : ℝ) - 1) * c := by
    have hs : (∑ j ∈ Finset.univ.erase i, ⟪v i, v j⟫_ℝ) ≤
        ∑ _j ∈ Finset.univ.erase i, c :=
      Finset.sum_le_sum fun j hj => hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      rw [Nat.cast_sub hn]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [real_inner_self_eq_norm_sq]
    linarith [hdiag i]
  rw [← real_inner_self_eq_norm_sq, inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, v j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * (1 + ((n : ℝ) - 1) * c)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = c + (1 - c) / n := by field_simp; ring

lemma replicaMean_norm_le_one {n : ℕ} (hn : 0 < n) (v : Fin n → H)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1) : ‖replicaMean v‖ ≤ 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hsum : ‖∑ i, v i‖ ≤ (n : ℝ) := by
    calc
      ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        nlinarith [hdiag i, norm_nonneg (v i)]
      _ = n := by simp
  calc
    ‖replicaMean v‖ = (n : ℝ)⁻¹ * ‖∑ i, v i‖ := by
      simp [replicaMean, norm_smul]
    _ ≤ (n : ℝ)⁻¹ * n := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ hn0

lemma inner_replicaMean_le {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, ⟪v i, w j⟫_ℝ ≤ a) : ⟪replicaMean v, replicaMean w⟫_ℝ ≤ a := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = a := by field_simp

lemma le_inner_replicaMean {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, a ≤ ⟪v i, w j⟫_ℝ) : a ≤ ⟪replicaMean v, replicaMean w⟫_ℝ := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    a = (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := by field_simp
    _ ≤ (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)

lemma duplicate_ordered_blocks_bound {n : ℕ} (hn : 0 < n) (v : Fin 3 → Fin n → H)
    {a b c t : ℝ} (hab : a ≤ b)
    (hdiag : ∀ k i, ‖v k i‖ ^ 2 ≤ 1)
    (hoff : ∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ t)
    (h12 : ∀ i j, ⟪v 0 i, v 1 j⟫_ℝ ≤ a)
    (h13 : ∀ i j, b ≤ ⟪v 0 i, v 2 j⟫_ℝ)
    (h23 : ∀ i j, c ≤ ⟪v 1 i, v 2 j⟫_ℝ) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let x := replicaMean (v 0)
  let y := replicaMean (v 1)
  let z := replicaMean (v 2)
  have hx := replicaMean_norm_le_one hn (v 0) (hdiag 0)
  have hy := replicaMean_norm_sq_le hn (v 1) (hdiag 1) (hoff 1)
  have hz := replicaMean_norm_sq_le hn (v 2) (hdiag 2) (hoff 2)
  have hxy : ⟪x, y⟫_ℝ ≤ a := inner_replicaMean_le hn _ _ h12
  have hxz : b ≤ ⟪x, z⟫_ℝ := le_inner_replicaMean hn _ _ h13
  have hyz : c ≤ ⟪y, z⟫_ℝ := le_inner_replicaMean hn _ _ h23
  change ‖x‖ ≤ _ at hx
  change ‖y‖ ^ 2 ≤ _ at hy
  change ‖z‖ ^ 2 ≤ _ at hz
  have hx1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hdiff : ‖z - y‖ ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
    rw [norm_sub_sq_real, real_inner_comm]
    linarith
  have hinner : b - a ≤ ⟪x, z - y⟫_ℝ := by rw [inner_sub_right]; linarith
  have hnonneg : 0 ≤ ⟪x, z - y⟫_ℝ := by linarith
  have habsq : (b - a) ^ 2 ≤ ⟪x, z - y⟫_ℝ ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hab) hnonneg).mpr hinner
  have hcs : ⟪x, z - y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖z - y‖ ^ 2 := by
    have h := abs_real_inner_le_norm x (z - y)
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg _))).mpr h
    simpa only [sq_abs, mul_pow] using hs
  exact habsq.trans (hcs.trans ((mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)).trans
    (by simpa using hdiff)))

lemma posSemidef_standard_basis_inner {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (i j : Fin n) :
    letI := B.toSeminormedAddCommGroup hB
    letI := B.toInnerProductSpace hB
    ⟪(Pi.single i 1 : Fin n → ℝ), Pi.single j 1⟫_ℝ = B i j := by
  change (B *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1) = B i j
  simp

lemma triangleConstraints_measurable (a b c t : ℝ) (k l : Fin 3) :
    MeasurableSet (triangleConstraints a b c t k l) := by
  unfold triangleConstraints
  split_ifs <;> measurability

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

lemma triangleConstraints_diag (a b c t : ℝ) (k : Fin 3) :
    triangleConstraints a b c t k k = Iio t := by simp [triangleConstraints]

lemma triangleConstraints_cut {a : ℝ} (b c t : ℝ) (hat : a ≤ t) (k l : Fin 3) :
    triangleConstraints a b c t k l ⊆ Iio t := by
  unfold triangleConstraints
  split_ifs
  · exact Subset.rfl
  · exact Iio_subset_Iio hat
  · exact Ioo_subset_Iio_self
  · exact Ioo_subset_Iio_self

lemma tripleIndex_ne {n : ℕ} {k l : Fin 3} (hkl : k ≠ l) (i j : Fin n) :
    tripleIndex k i ≠ tripleIndex l j := by
  intro h
  have := congrArg (tripleLabels (3 * n)) h
  exact hkl (by simpa using this)

lemma tripleIndex_inj {n : ℕ} (k : Fin 3) {i j : Fin n} (hij : i ≠ j) :
    tripleIndex k i ≠ tripleIndex k j := by
  intro h
  apply hij
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp [tripleIndex] at h'
  omega

lemma triangle_pattern_psd_bound {n : ℕ} (hn : 0 < n)
    (B : OverlapBlock (3 * n)) (hB : Matrix.PosSemidef B)
    (hdiag : ∀ i, B i i ≤ 1) {a b c t : ℝ} (hab : a ≤ b)
    (hpattern : B ∈ patternMatrices (tripleLabels (3 * n)) (triangleConstraints a b c t)) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let _ := Matrix.toSeminormedAddCommGroup B hB
  let _ := Matrix.toInnerProductSpace B hB
  let v : Fin 3 → Fin n → (Fin (3 * n) → ℝ) := fun k i => Pi.single (tripleIndex k i) 1
  have hv (k l : Fin 3) (i j : Fin n) :
      ⟪v k i, v l j⟫_ℝ = B (tripleIndex k i) (tripleIndex l j) :=
    posSemidef_standard_basis_inner B hB _ _
  apply duplicate_ordered_blocks_bound hn v hab
  · intro k i
    rw [← real_inner_self_eq_norm_sq, hv]
    exact hdiag _
  · intro k i j hij
    rw [hv]
    have h := hpattern _ _ (tripleIndex_inj k hij)
    simp only [tripleLabels_tripleIndex, triangleConstraints_diag, mem_Iio] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 1) i j)
    simp [triangleConstraints] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (1 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le

theorem gg_triangle_pattern_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹'
      patternMatrices (tripleLabels 3) (triangleConstraints a b c t))) :
    (b - a) ^ 2 ≤ 2 * (t - c) := by
  have hall := gg_triple_pattern μ hEx hGG hSym (triangleConstraints a b c t)
    (triangleConstraints_measurable a b c t) t (triangleConstraints_diag a b c t)
    (triangleConstraints_cut b c t hat) hA
  have hbound (n : ℕ) : (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ)) := by
    have hpos := hall (3 * (n + 1)) (by omega)
    have hne : μ (overlapBlock id (3 * (n + 1)) ⁻¹'
        patternMatrices (tripleLabels (3 * (n + 1))) (triangleConstraints a b c t)) ≠ 0 := by
      intro hz
      simp [Measure.real, hz] at hpos
    obtain ⟨Q, hQ, hG, hD⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hne
      (ae_restrict_of_ae (hGram.and hdiag))
    have h := triangle_pattern_psd_bound (by omega : 0 < n + 1)
      (overlapBlock id (3 * (n + 1)) Q) (hG _) (fun i => hD i) hab hQ
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have ht : Tendsto (fun n : ℕ => 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ))) atTop
      (𝓝 (2 * (t - c))) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul (2 * (1 - t))
    have h' := h.const_add (2 * (t - c))
    simpa only [mul_zero, add_zero, mul_one_div, mul_div_assoc] using h'
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

lemma triangleEvent_pattern {a b c t : ℝ} (hat : a ≤ t) (Q : OverlapArray)
    (hSym : ∀ i j, Q i j = Q j i) (hQ : Q ∈ triangleEvent a b c t) :
    overlapBlock id 3 Q ∈ patternMatrices (tripleLabels 3) (triangleConstraints a b c t) := by
  have h10 := hSym 1 0
  have h20 := hSym 2 0
  have h21 := hSym 2 1
  have hQt : Q 0 1 < t := hQ.1.trans_le hat
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [overlapBlock, tripleLabels, triangleConstraints, triangleEvent]

lemma gg_triangleEvent_null (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t) (hgap : 2 * (t - c) < (b - a) ^ 2) :
    μ (triangleEvent a b c t) = 0 := by
  by_contra hne
  have hpos : 0 < μ.real (triangleEvent a b c t) :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hle : μ.real (triangleEvent a b c t) ≤ μ.real
      (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) (triangleConstraints a b c t)) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hSym] with Q hQ
    exact triangleEvent_pattern hat Q hQ
  exact hgap.not_ge (gg_triangle_pattern_bound μ hEx hGG hSym hGram hdiag hab hat (hpos.trans_le hle))

lemma exists_rational_triangle_box {x y z : ℝ} (hxy : x < y) (hyz : y ≤ z) :
    ∃ a b c t : ℚ, (a : ℝ) ≤ b ∧ (a : ℝ) ≤ t ∧
      2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 ∧
      x < a ∧ (b : ℝ) < y ∧ y < t ∧ (c : ℝ) < z ∧ z < t := by
  obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hxy
  obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
  have hδ : 0 < ((b : ℝ) - a) ^ 2 / 8 := by positivity
  obtain ⟨c, hzc, hcz⟩ := exists_rat_btwn (show z - ((b : ℝ) - a) ^ 2 / 8 < z by linarith)
  obtain ⟨t, hzt, htz⟩ := exists_rat_btwn (show z < z + ((b : ℝ) - a) ^ 2 / 8 by linarith)
  refine ⟨a, b, c, t, hab.le, (hay.trans_le hyz).le.trans hzt.le, ?_, hxa, hby,
    hyz.trans_lt hzt, hcz, hzt⟩
  nlinarith

lemma gg_no_ordered_crossing (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ (Q 0 1 < Q 0 2 ∧ Q 0 2 ≤ Q 1 2) := by
  have hBoxes : ∀ᵐ Q ∂μ, ∀ a b c t : ℚ,
      (a : ℝ) ≤ b → (a : ℝ) ≤ t → 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 →
      Q ∉ triangleEvent a b c t := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro c
    apply ae_all_iff.mpr
    intro t
    by_cases hab : (a : ℝ) ≤ b
    · by_cases hat : (a : ℝ) ≤ t
      · by_cases hgap : 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2
        · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
            (gg_triangleEvent_null μ hEx hGG hSym hGram hdiag hab hat hgap)] with Q hQ
          exact fun _ _ _ => hQ
        · exact Eventually.of_forall fun _ _ _ h => (hgap h).elim
      · exact Eventually.of_forall fun _ _ h => (hat h).elim
    · exact Eventually.of_forall fun _ h => (hab h).elim
  filter_upwards [hBoxes] with Q hQ
  rintro ⟨hxy, hyz⟩
  obtain ⟨a, b, c, t, hab, hat, hgap, hbox⟩ := exists_rational_triangle_box hxy hyz
  exact hQ a b c t hab hat hgap hbox

lemma gram_array_symmetric (Q : OverlapArray)
    (hGram : ∀ n, Matrix.PosSemidef (overlapBlock id n Q)) : ∀ i j, Q i j = Q j i := by
  intro i j
  let n := max i j + 1
  let a : Fin n := ⟨i, by dsimp [n]; omega⟩
  let b : Fin n := ⟨j, by dsimp [n]; omega⟩
  have h := (hGram n).isHermitian.apply b a
  simpa [overlapBlock, a, b] using h

theorem gg_ultrametric (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, min (Q 0 1) (Q 0 2) ≤ Q 1 2 := by
  have hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i :=
    hGram.mono fun Q hQ => gram_array_symmetric Q hQ
  have hno := gg_no_ordered_crossing μ hEx hGG hSym hGram hdiag
  have hno' := (hEx 0 1).quasiMeasurePreserving.ae hno
  have hsmall : ∀ᵐ Q ∂μ, min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
    filter_upwards [hno, hno', hSym] with Q hQ hQ' hs
    simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide] at hQ'
    rw [hs 1 0] at hQ'
    by_cases h : Q 0 2 ≤ Q 1 2
    · rw [min_eq_left h]
      exact le_of_not_gt fun hh => hQ ⟨hh, h⟩
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h']
      exact le_of_not_gt fun hh => hQ' ⟨hh, h'⟩
  have hsmall' := (hEx 0 2).quasiMeasurePreserving.ae hsmall
  filter_upwards [hsmall', hSym] with Q hQ hs
  simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
    show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide] at hQ
  simpa only [hs 2 0, hs 1 0, hs 2 1, min_comm] using hQ

lemma scalarArray_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (scalarArray f) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarBlock_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) {n : ℕ} :
    Measurable (scalarBlock f (n := n)) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarArray_swap_invariant (μ : Measure PairedOverlapArray)
    (hEx : PairedSwapInvariant μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    OverlapSwapInvariant (μ.map (scalarArray f)) := by
  intro i j
  have heq : relabelArray (Equiv.swap i j) ∘ scalarArray f =
      scalarArray f ∘ pairedRelabel (Equiv.swap i j) := rfl
  refine ⟨Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _), ?_⟩
  rw [Measure.map_map _ (scalarArray_measurable hf), heq,
    ← Measure.map_map (scalarArray_measurable hf) (hEx i j).measurable,
    (hEx i j).map_eq]
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma scalarArray_gg (μ : Measure PairedOverlapArray)
    (hGG : JointGhirlandaGuerra μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    GhirlandaGuerra (μ.map (scalarArray f)) id := by
  intro n hn i s hs t ht
  have hblock : Measurable (overlapBlock (id : OverlapArray → OverlapArray) n) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hedge (i j : ℕ) : Measurable (fun Q : OverlapArray => Q i j) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hmap (u : Set OverlapArray) (hu : MeasurableSet u) :
      (μ.map (scalarArray f)).real u = μ.real (scalarArray f ⁻¹' u) := by
    rw [measureReal_def, Measure.map_apply (scalarArray_measurable hf) hu]
    rfl
  simp only [id_eq]
  rw [hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i n ∈ t})
      ((hs.preimage hblock).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hblock), hmap {Q | Q 0 1 ∈ t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i j ∈ t})
    ((hs.preimage hblock).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact hGG n hn i (scalarBlock f ⁻¹' s) (hs.preimage (scalarBlock_measurable hf))
    (f ⁻¹' t) (ht.preimage hf)

lemma measurableSet_gram_arrays :
    MeasurableSet {Q : OverlapArray | ∀ n, Matrix.PosSemidef (overlapBlock id n Q)} := by
  apply IsClosed.measurableSet
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  have hiff (Q : OverlapArray) :=
    Matrix.posSemidef_iff_dotProduct_mulVec (M := overlapBlock id n Q)
  simp_rw [hiff]
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · change IsClosed {Q : OverlapArray | Matrix.conjTranspose (overlapBlock id n Q) = overlapBlock id n Q}
    apply isClosed_eq <;> unfold overlapBlock <;> fun_prop
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold overlapBlock
    fun_prop

lemma scalarArray_ultrametric (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, min (f (Q 0 1)) (f (Q 0 2)) ≤ f (Q 1 2) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hu := gg_ultrametric ν (scalarArray_swap_invariant μ hEx hf)
    (scalarArray_gg μ hGG hf) hg hd
  exact ae_of_ae_map hm.aemeasurable hu

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_norm (a : ℝ) : Integrable (fun y : E => Real.exp (a*‖y‖)) μ := by
  obtain ⟨c,hc,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hh (y : E) : a*‖y‖ ≤ c*‖y‖^2+a^2/(4*c) := by
    have h := sq_nonneg (2*c*‖y‖-a)
    have hd : a^2/(4*c)*(4*c)=a^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply (hI.const_mul (Real.exp (a^2/(4*c)))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hh y]

lemma gaussian_integrable_exp_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a σ : ℝ) (x : E) :
    Integrable (fun y : E => Real.exp (a*f (x+σ • y))) μ := by
  have hbound (y : E) : a*f (x+σ • y) ≤ |a| *|f x|+(|a| *L*|σ|)*‖y‖ := by
    have hl := hf.dist_le_mul (x+σ • y) x
    simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hl
    have hn := abs_add_le (f (x+σ • y)-f x) (f x)
    rw [sub_add_cancel] at hn
    have hmul := mul_le_mul_of_nonneg_left (le_trans hn (add_le_add hl le_rfl)) (abs_nonneg a)
    have hle := le_abs_self (a*f (x+σ • y))
    rw [abs_mul] at hle
    nlinarith
  have hfc := hf.continuous
  apply ((gaussian_integrable_exp_norm μ (|a| *L*|σ|)).const_mul
    (Real.exp (|a| *|f x|))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    exact Real.exp_le_exp.mpr (hbound y)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

lemma integrable_of_all_exp (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) :
    Integrable X μ :=
  (memLp_of_mem_interior_integrableExpSet (mem_interior_integrableExpSet_of_all μ hX 0) 1).integrable (by simp)

omit [IsProbabilityMeasure μ] in
lemma all_exp_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) (c : ℝ) :
    ∀ t : ℝ, Integrable (fun ω => Real.exp (t*(X ω+c))) μ := by
  intro t
  simpa only [mul_add,Real.exp_add] using (hX t).mul_const (Real.exp (t*c))

lemma entropicMean_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (p c : ℝ) : entropicMean μ p (fun ω => X ω+c)=entropicMean μ p X+c := by
  by_cases hp : p=0
  · subst p
    rw [entropicMean_zero μ (all_exp_add_const μ hX c),entropicMean_zero μ hX,
      integral_add (integrable_of_all_exp μ hX) (integrable_const c),integral_const]
    simp
  · rw [entropicMean_eq_div μ (all_exp_add_const μ hX c) hp,entropicMean_eq_div μ hX hp]
    simp only [cgf,mgf_add_const]
    rw [Real.log_mul (ne_of_gt (mgf_pos (hX p))) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
    field_simp

lemma entropicMean_mono_variable
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    (hXY : X ≤ᵐ[μ] Y) {p : ℝ} (hp : 0 ≤ p) :
    entropicMean μ p X ≤ entropicMean μ p Y := by
  rcases hp.eq_or_lt with hp|hp
  · subst p
    rw [entropicMean_zero μ hX,entropicMean_zero μ hY]
    exact integral_mono_ae (integrable_of_all_exp μ hX) (integrable_of_all_exp μ hY) hXY
  · rw [entropicMean_eq_div μ hX (ne_of_gt hp),entropicMean_eq_div μ hY (ne_of_gt hp)]
    apply div_le_div_of_nonneg_right _ hp.le
    exact Real.log_le_log (mgf_pos (hX p)) (mgf_mono_of_nonneg hXY hp.le (hY p))

lemma entropicMean_bounded_difference
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    {C p : ℝ} (hp : 0 ≤ p) (hXY : ∀ᵐ ω ∂μ, |X ω-Y ω| ≤ C) :
    |entropicMean μ p X-entropicMean μ p Y| ≤ C := by
  have h1 : X ≤ᵐ[μ] (fun ω => Y ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).2
    linarith
  have h2 : Y ≤ᵐ[μ] (fun ω => X ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).1
    linarith
  have H1 := entropicMean_mono_variable μ hX (all_exp_add_const μ hY C) h1 hp
  have H2 := entropicMean_mono_variable μ hY (all_exp_add_const μ hX C) h2 hp
  rw [entropicMean_add_const μ hY] at H1
  rw [entropicMean_add_const μ hX] at H2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianMarkRecursion
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
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_linear_shift {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (A : E →L[ℝ] E) (a : ℝ) (x : E) :
    Integrable (fun y => Real.exp (a*f (x+A y))) μ := by
  have hA : LipschitzWith ‖A‖₊ (fun y => x+A y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using A.lipschitz.dist_le_mul y z
  have hg := hf.comp hA
  simpa using gaussian_integrable_exp_lipschitz μ hg a 1 (0:E)

lemma gaussianLinearEntropic_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {b : ℝ} (hb : 0 ≤ b) (A : E →L[ℝ] E) :
    LipschitzWith L (gaussianLinearEntropic μ b A f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,gaussianLinearEntropic]
  apply entropicMean_bounded_difference μ
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a x)
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a y) hb
  exact ae_of_all _ fun z => by
    simpa only [Real.dist_eq,dist_add_right] using hf.dist_le_mul (x+A z) (y+A z)

lemma gaussianLinearBackward_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (l : List (ℝ×(E →L[ℝ] E)))
    (hl : ∀ c ∈ l, 0 ≤ c.1) : LipschitzWith L (gaussianLinearBackward μ l f) := by
  induction l with
  | nil => exact hf
  | cons c l ih =>
    exact gaussianLinearEntropic_lipschitz μ
      (ih (fun d hd => hl d (List.mem_cons_of_mem c hd))) (hl c List.mem_cons_self) c.2

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
lemma gaussianLinearMarkStep_measurable (A : ℕ → E →L[ℝ] E) :
    Measurable (gaussianLinearMarkStep A) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply (j+1)).comp measurable_fst).add
    ((A j).measurable.comp measurable_snd)

omit [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma linearCascadeWord_nonneg (A : ℕ → E →L[ℝ] E) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∀ c ∈ linearCascadeWord A k z, 0 ≤ c.1 := by
  induction k with
  | zero => simp [linearCascadeWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma gaussianLinearRecursion_realization (ν : ProbabilityMeasure E) [IsGaussian (ν:Measure E)]
    (A : ℕ → E →L[ℝ] E) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ x, finiteCascadeLogRecursion ν (gaussianLinearMarkStep A) k z (fun x => f (x 0)) x=
        gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k z) f (x k)) ∧
    finiteCascadeFractionalIntegrable ν (gaussianLinearMarkStep A) (fun x => f (x 0)) k z := by
  induction k with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ k ih =>
    have H := ih (fun i => z i.succ) (fun i => hz i.succ)
    let g := gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k (fun i => z i.succ)) f
    have hg : LipschitzWith L g := gaussianLinearBackward_lipschitz (ν:Measure E) hf _
      (linearCascadeWord_nonneg A k _ (fun i => (hz i.succ).le))
    constructor
    · intro x
      simp only [finiteCascadeLogRecursion,fractionalLogMoment,H.1,gaussianLinearMarkStep,
        linearCascadeWord,gaussianLinearBackward,gaussianLinearEntropic]
      rw [entropicMean_eq_div (ν:Measure E)
        (fun a => gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) a (x (k+1)))
        (hz 0).ne']
      rfl
    · constructor
      · intro x
        simp only [H.1,gaussianLinearMarkStep]
        exact gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) (z 0) (x (k+1))
      · exact H.2

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianMarks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma countableCoordinate_injective {ι : Type*} [Countable ι] :
    Function.Injective (countableCoordinate (ι := ι)) := by
  let := Encodable.ofCountable ι
  exact Encodable.encode_injective

lemma indexedLeafSharedVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafSharedVertex n l) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [indexedLeafSharedVertex] at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [indexedLeafSharedVertex] at hij
    | succ j =>
      simpa only [Fin.succ_inj] using indexedLeafVertex_injective n l
        (by simpa [indexedLeafSharedVertex] using hij)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteGaussianRow
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {K : Type*} [Fintype K]

lemma finiteGaussianRow_key {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (k : K) :
    finiteGaussianRow key a (key k) = a k := by
  classical
  simp [finiteGaussianRow,hk.eq_iff]

lemma finiteGaussianRow_zero {key : K → ℕ} (a : K → ℝ) (i : ℕ)
    (hi : ∀ k, key k ≠ i) : finiteGaussianRow key a i = 0 := by
  simp [finiteGaussianRow,hi]

lemma finiteGaussianRow_key_lt (key : K → ℕ) (k : K) :
    key k < finiteGaussianRowLength key :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))

lemma finiteGaussianRow_tail (key : K → ℕ) (a : K → ℝ) (i : ℕ)
    (hi : finiteGaussianRowLength key ≤ i) : finiteGaussianRow key a i = 0 := by
  apply finiteGaussianRow_zero a i
  intro k
  have h := finiteGaussianRow_key_lt key k
  omega

lemma finiteGaussianRow_sum {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ)
    (F : ℕ → ℝ → ℝ) (hF : ∀ i, F i 0 = 0) :
    (∑ i : Fin (finiteGaussianRowLength key), F i.val (finiteGaussianRow key a i.val)) =
      ∑ k, F (key k) (a k) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => F i (finiteGaussianRow key a i))]
  have hs : Finset.univ.image key ⊆ Finset.range (finiteGaussianRowLength key) := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (finiteGaussianRow_key_lt key k)
  rw [← Finset.sum_subset hs]
  · rw [Finset.sum_image hk.injOn]
    simp_rw [finiteGaussianRow_key hk]
  · intro i hi hi'
    rw [finiteGaussianRow_zero a i,hF]
    intro k hki
    exact hi' (Finset.mem_image.mpr ⟨k,Finset.mem_univ k,hki⟩)

end
variable {I : Type} [Fintype I]

lemma indexedGaussianRowKey_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedGaussianRowKey (I := I) n l) := by
  intro a b hab
  have h := countableCoordinate_injective hab
  exact Prod.ext (indexedLeafSharedVertex_injective n l (congrArg Prod.fst h)) (congrArg (fun q : SharedVertex n × I => q.2) h)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
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

lemma finite_profile_telescope {k : ℕ} (q : Fin (k+1) → ℝ) :
    q 0 + ∑ i : Fin k, (q i.succ-q i.castSucc) = q (Fin.last k) := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

lemma profileGaussian_coefficient {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) :
    hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) =
      Fin.cases (fun i => Real.sqrt (q 0 i))
        (fun l i => Real.sqrt (q l.succ i-q l.castSucc i)) := by
  funext l i
  induction l using Fin.cases with
  | zero => rfl
  | succ l =>
    simp only [hierarchyRowCoefficients,Fin.cases_succ,profileGaussianStep,
      dite_eq_left (show k-1-l.val<k by omega)]
    congr 2 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_succ,Fin.val_castSucc] <;> omega

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

lemma indexedLeafVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin n) :
    indexedVertexDepth n (indexedLeafVertex n l i) = i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [indexedLeafVertex,Fin.cases_succ,indexedVertexDepth] using congrArg Fin.succ (ih l.2.2 i)

lemma indexedLeafSharedVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin (n+1)) :
    indexedSharedVertexDepth n (indexedLeafSharedVertex n l i) = i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => simpa only [indexedLeafSharedVertex,Fin.cases_succ,indexedSharedVertexDepth] using
      congrArg Fin.succ (indexedLeafVertex_depth n l i)

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

lemma indexedLeafSharedVertex_eq_iff_pair (n : ℕ) (l m : IndexedLeaf n) (i j : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m j ↔ i=j ∧ i ≤ indexedCommonDepth n l m := by
  constructor
  · intro h
    have he : i=j := by
      have hh := congrArg (indexedSharedVertexDepth n) h
      simpa only [indexedLeafSharedVertex_depth] using hh
    subst j
    exact ⟨rfl,(indexedLeafSharedVertex_eq_iff n l m i).mp h⟩
  · rintro ⟨rfl,h⟩
    exact (indexedLeafSharedVertex_eq_iff n l m i).mpr h

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_eventually_eq (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) :
    ∀ᶠ n in atTop, gaussianPrefixCovariance v w L n x y=countableGaussianCovariance v w L x y := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn
  unfold gaussianPrefixCovariance countableGaussianCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) n]
  have he (i : ℕ) : maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y =
      if i<L x then w i x*maskedGaussianCoefficient v L i y else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_range_cutoff,min_eq_right hn]
  unfold gaussianPrefixCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) (L x)]
  simp_rw [he,sum_range_cutoff,min_self]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_mask (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (i : ℕ) (x : S×IndexedLeaf n) :
    maskedGaussianCoefficient (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) i x =
      indexedGaussianRow n B V i x := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · rfl
  · exact (finiteGaussianRow_tail _ _ i (Nat.le_of_not_gt hi)).symm

lemma indexedGaussianRowKey_eq (n : ℕ) (l m : IndexedLeaf n) (a b : Fin (n+1)×I) :
    indexedGaussianRowKey n m b = indexedGaussianRowKey n l a ↔
      b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n m l := by
  rw [indexedGaussianRowKey,indexedGaussianRowKey,countableCoordinate_injective.eq_iff,
    Prod.mk.injEq,indexedLeafSharedVertex_eq_iff_pair]
  constructor
  · rintro ⟨⟨he,hc⟩,hi⟩
    exact ⟨he,hi,he ▸ hc⟩
  · rintro ⟨he,hi,hc⟩
    exact ⟨⟨he,he.symm ▸ hc⟩,hi⟩

omit [MeasurableSpace S] in
lemma indexedGaussianRow_cross_value (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) (a : Fin (n+1)×I) :
    indexedGaussianRow n B V (indexedGaussianRowKey n x.2 a) y =
      if a.1 ≤ indexedCommonDepth n y.2 x.2 then B a.1 a.2*V y.1 a.2 else 0 := by
  classical
  unfold indexedGaussianRow finiteGaussianRow
  simp_rw [indexedGaussianRowKey_eq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hd : ¬ (b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n y.2 x.2) := by
      rintro ⟨h1,h2,_⟩
      exact hba (Prod.ext h1 h2)
    simp [hd]
  · simp

omit [MeasurableSpace S] in
lemma indexedGaussianRow_covariance (n : ℕ) (B C : Fin (n+1) → I → ℝ)
    (V W : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n B V) (indexedGaussianRow n C W)
      (indexedGaussianRowLength (I := I) n) x y =
      ∑ i : I, (∑ j : Fin (n+1), if j ≤ indexedCommonDepth n y.2 x.2 then C j i*B j i else 0)*W x.1 i*V y.1 i := by
  classical
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [indexedGaussianRow_mask]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => C p.1 p.2*W x.1 p.2) i.val*
      indexedGaussianRow n B V i.val y) = _
  rw [finiteGaussianRow_sum (indexedGaussianRowKey_injective n x.2) _
    (fun i z => z*indexedGaussianRow n B V i y) (fun i => zero_mul _)]
  simp_rw [indexedGaussianRow_cross_value]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

end

lemma finite_profile_prefix {k : ℕ} (q : Fin (k+1) → ℝ) (a : Fin (k+1)) :
    q 0 + ∑ j : Fin k, (if j.succ ≤ a then q j.succ-q j.castSucc else 0) = q a := by
  have he (j : Fin k) : (if j.succ ≤ a then q j.succ-q j.castSucc else 0) =
      q (min j.succ a)-q (min j.castSucc a) := by
    by_cases hj : j.succ ≤ a
    · rw [ite_eq_left hj,min_eq_left hj,min_eq_left ((Fin.castSucc_le_succ j).trans hj)]
    · have hc : a ≤ j.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ] at *
        omega
      rw [ite_eq_right hj,min_eq_right (le_of_not_ge hj),min_eq_right hc,sub_self]
  simp_rw [he]
  simpa only [min_eq_left (Fin.zero_le a),min_eq_right (Fin.le_last a)] using
    finite_profile_telescope (fun l => q (min l a))

lemma profileGaussian_coefficient_prefix {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (a : Fin (k+1)) (i : I) :
    (∑ l : Fin (k+1), if l ≤ a then
      hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2 else 0) = q a i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.zero_le,ite_true,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (Fin.castSucc_le_succ j)))
  simp_rw [he]
  exact finite_profile_prefix (fun l => q l i) a

lemma profileGaussianRow_covariance {I S : Type} [Fintype I] [MeasurableSpace S]
    {k : ℕ} (q : Fin (k+1) → I → ℝ) (h0 : ∀ i, 0 ≤ q 0 i)
    (hq : ∀ i, Monotone (fun l => q l i)) (V W : S → EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V)
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) W)
      (indexedGaussianRowLength (I := I) k) x y =
      ∑ i : I, q (indexedCommonDepth k y.2 x.2) i*W x.1 i*V y.1 i := by
  rw [indexedGaussianRow_covariance]
  simp_rw [← sq,profileGaussian_coefficient_prefix q h0 hq]

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
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma countableGaussianCovariance_posSemidef {S : Type*} [MeasurableSpace S]
    (v : ℕ → S → ℝ) (L : S → ℕ) (r : ℕ) (x : Fin r → S) :
    Matrix.PosSemidef (fun i j => countableGaussianCovariance v v L (x i) (x j)) := by
  classical
  have he : ∀ᶠ n in atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (x i) (x j) = countableGaussianCovariance v v L (x i) (x j) := by
    simp only [Filter.eventually_all]
    exact fun i j => gaussianPrefixCovariance_eventually_eq v v L (x i) (x j)
  obtain ⟨n,hn⟩ := he.exists
  let A : Matrix (Fin n) (Fin r) ℝ := fun a i => maskedGaussianCoefficient v L a.val (x i)
  have hp := Matrix.posSemidef_conjTranspose_mul_self A
  have hm : (fun i j => countableGaussianCovariance v v L (x i) (x j)) = Aᴴ * A := by
    funext i j
    rw [← hn i j]
    simp only [gaussianPrefixCovariance,A]
    rfl
  rw [hm]
  exact hp

lemma sourceSpinArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).1:ℝ)) := by
  exact Matrix.posSemidef_gram ℝ (fun i : Fin r => (x i).1.val)

lemma sourceTreeArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).2:ℝ)) := by
  let q : Fin (k+1) → Fin 1 → ℝ := fun l _ => (l.val:ℝ)/(k+1:ℕ)
  let V : NormalizedSpin N → EuclideanSpace ℝ (Fin 1) := fun _ => WithLp.toLp 2 (fun _ => 1)
  let v := indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V
  have hq : ∀ i, Monotone (fun l => q l i) := by
    intro i a b hab
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  have he (i j : Fin r) : countableGaussianCovariance v v
      (indexedGaussianRowLength (I := Fin 1) k) (x i) (x j) = ((sourceJointArray x i j).2:ℝ) := by
    rw [profileGaussianRow_covariance q (by intro; simp [q]) hq V V]
    simp [q,V,sourceJointArray,sourceJointOverlap]
  have hp := countableGaussianCovariance_posSemidef v
    (indexedGaussianRowLength (I := Fin 1) k) r (fun i => x i)
  simpa only [he] using hp

lemma sourceJointArray_diagonal {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (i : ℕ) :
    ((sourceJointArray x i i).1:ℝ) = 1 := by
  change inner ℝ (x i).1.val (x i).1.val = 1
  have hx : ‖(x i).1.val‖=1 := by simp
  simp [hx]

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

lemma sourceGibbsArray_exchangeable (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _) := by
  have hr := annealedInfiniteReplica_reindex (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u) e
  have hm : Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) :=
    (sourceJointArray_measurable (n+1) k).comp measurable_snd
  refine ⟨(compactRelabel_continuous e).measurable, ?_⟩
  change Measure.map _ (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) = _
  rw [Measure.map_map (compactRelabel_continuous e).measurable hm]
  change Measure.map ((fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ∘
    (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => (a.1,fun i => a.2 (e i)))) _ = _
  rw [← Measure.map_map hm hr.measurable,hr.map_eq]
  rfl

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactJointMonomials
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

lemma compactJointMonomial_zero : compactJointMonomial 0 0 = 1 := by ext x; simp

lemma compactJointMonomial_add (p d p' d' : ℕ) :
    compactJointMonomial (p+p') (d+d') = compactJointMonomial p d * compactJointMonomial p' d' := by
  ext x
  simp only [compactJointMonomial_apply,BoundedContinuousFunction.mul_apply,pow_add]
  ring

lemma compactJointMonomial_separates (x y : CompactJointOverlap) (h : x≠y) :
    ∃ p d, compactJointMonomial p d x ≠ compactJointMonomial p d y := by
  by_contra hn
  push Not at hn
  apply h
  apply Prod.ext <;> apply Subtype.ext
  · simpa using hn 1 0
  · simpa using hn 0 1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGDensity
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

section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

lemma compactGGTestCLM_apply {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    compactGGTestCLM μ n i f g = compactGGDefect μ n i f g := by
  classical
  simp [compactGGTestCLM,compactGGDefect,boundedTestIntegral]

lemma compactJoint_monomials_total (L : (CompactJointOverlap →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ p d, L (compactJointMonomial p d)=0) : L=0 := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact CompactJointOverlap ℝ ℝ
  let L' := L.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let m (a : ℕ×ℕ) : C(CompactJointOverlap,ℝ) := (compactJointMonomial a.1 a.2).toContinuousMap
  have hm0 : m 0=1 := by ext x; simp [m]
  have hmadd (a b : ℕ×ℕ) : m (a+b)=m a*m b := by
    ext x
    exact congrArg (fun f : CompactJointOverlap →ᵇ ℝ => f x) (compactJointMonomial_add _ _ _ _)
  let M : Submonoid C(CompactJointOverlap,ℝ) :=
    { carrier := Set.range m
      one_mem' := ⟨0,hm0⟩
      mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,hmadd a b⟩ }
  let A := Algebra.adjoin ℝ (M : Set C(CompactJointOverlap,ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨p,d,hpd⟩ := compactJointMonomial_separates x y hxy
    have hmem : m (p,d) ∈ A :=
      Algebra.subset_adjoin (show m (p,d) ∈ M from ⟨(p,d),rfl⟩)
    exact ⟨m (p,d),⟨m (p,d),hmem,rfl⟩,hpd⟩
  have hA : (A : Set C(CompactJointOverlap,ℝ)) ⊆ (L'.ker : Set C(CompactJointOverlap,ℝ)) := by
    have hspan : Submodule.span ℝ (M : Set C(CompactJointOverlap,ℝ)) ≤ L'.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨p,d⟩,rfl⟩
      change L (e ((compactJointMonomial p d).toContinuousMap)) = 0
      have he : e ((compactJointMonomial p d).toContinuousMap) = compactJointMonomial p d := by
        ext x; rfl
      rw [he]
      exact hL p d
    intro f hf
    apply hspan
    change f ∈ A.toSubmodule at hf
    simpa only [A,Algebra.adjoin_eq_span,Submonoid.closure_eq] using hf
  have hclosed := L'.isClosed_ker
  have hc := closure_minimal hA hclosed
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hall (f : C(CompactJointOverlap,ℝ)) : L' f=0 := by
    apply hc
    change f ∈ A.topologicalClosure
    rw [htop]
    trivial
  ext g
  have h := hall (e.symm g)
  simpa [L'] using h

lemma compactGG_of_joint_monomials (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
    (h : ∀ p d, compactGGDefect μ n i f (compactJointMonomial p d)=0)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect μ n i f g=0 := by
  have hz := compactJoint_monomials_total (compactGGTestCLM μ n i f)
    (fun p d => (compactGGTestCLM_apply μ n i f _).trans (h p d))
  rw [← compactGGTestCLM_apply,hz]
  rfl

end

lemma compactGGDefect_one (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    compactGGDefect μ r i G 1=0 := by
  have hr : 1 ≤ r := by have := i.isLt; omega
  simp only [compactGGDefect,BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one,
    integral_const,probReal_univ,smul_eq_mul,Finset.sum_const,Finset.card_erase_of_mem
    (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sub hr,Nat.cast_one]
  ring

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ) (z : Fin k→ℝ)
variable (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
variable (t : ℕ→ℝ≥0) (h : ℕ→Fin (k+1)→ℝ)
variable (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n, u n∈Icc (fun _=>1) (fun _=>2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j=>p j.val) (fun j=>d j.val) (h n) z (t n) v)
  (Icc (fun _ : Fin (n+1)=>1) (fun _=>2)) (u n))
variable {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht in
lemma source_contact_limit_joint_gg
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (fun a=>p a.val) (fun a=>d a.val)
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν))
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect ν r i G g=0 := by
  apply compactGG_of_joint_monomials ν r i G
  intro a b
  by_cases hab : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    subst a b
    simpa only [compactJointMonomial_zero] using compactGGDefect_one ν r i G
  obtain ⟨j,hp,hd⟩ := hcover a b (by omega)
  apply compactGGDefect_limit hlim
  simpa only [hp,hd,Function.comp_def] using
    (source_contact_monomial_tendsto k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht j r i G).comp hs.tendsto_atTop

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

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayLimitGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGibbsArray_closed_full (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    {F : Set (CompactArray CompactJointOverlap)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→NormalizedSpin (n+1)×IndexedLeaf k, sourceJointArray x ∈ F) :
    sourceGibbsArrayLaw n k f p d h u z t F=1 := by
  have hp : (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ⁻¹' F=univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) F=1
  rw [Measure.map_apply (show Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) from
      (sourceJointArray_measurable (n+1) k).comp measurable_snd) hF.measurableSet,hp]
  exact measure_univ

lemma compact_spin_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma compact_tree_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma sourceGibbsArray_limit_gram (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)) ∧
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)) := by
  constructor
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_spin_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_spin_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_spin_gram_closed r) (fun x => sourceSpinArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_tree_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_tree_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_tree_gram_closed r) (fun x => sourceTreeArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

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

lemma compactPairReal_measurable : Measurable compactPairReal := by unfold compactPairReal; fun_prop
lemma compactArrayReal_measurable : Measurable compactArrayReal := by
  unfold compactArrayReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))
lemma compactBlockReal_measurable (n : ℕ) : Measurable (compactBlockReal (n:=n)) := by
  unfold compactBlockReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))

instance compactRealLaw_probability (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure (compactRealLaw μ) :=
  (Measure.isProbabilityMeasure_map_iff compactArrayReal_measurable.aemeasurable).2 inferInstance

lemma compactRealLaw_gg (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0) :
    JointGhirlandaGuerra (compactRealLaw μ) := by
  intro n hn i s hs t ht
  have hb : Measurable (pairedBlock n) := by unfold pairedBlock; fun_prop
  have hedge (a b : ℕ) : Measurable (fun Q : PairedOverlapArray => Q a b) := by fun_prop
  have hmap (u : Set PairedOverlapArray) (hu : MeasurableSet u) :
      (compactRealLaw μ).real u=(μ : Measure _).real (compactArrayReal ⁻¹' u) :=
    map_measureReal_apply compactArrayReal_measurable hu
  rw [hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i n∈t}) ((hs.preimage hb).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hb), hmap {Q | Q 0 1∈t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i j∈t})
    ((hs.preimage hb).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact compactGG_events μ n (by omega) i (hGG n i)
    (compactBlockReal ⁻¹' s) (hs.preimage (compactBlockReal_measurable n))
    (compactPairReal ⁻¹' t) (ht.preimage compactPairReal_measurable)

lemma compactRealLaw_exchangeable (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _)) :
    PairedSwapInvariant (compactRealLaw μ) := by
  intro i j
  have hp : Measurable (pairedRelabel (Equiv.swap i j)) := by unfold pairedRelabel; fun_prop
  refine ⟨hp,?_⟩
  unfold compactRealLaw
  rw [Measure.map_map hp compactArrayReal_measurable]
  change Measure.map (compactArrayReal ∘ compactRelabel (Equiv.swap i j)) _ = _
  rw [← Measure.map_map compactArrayReal_measurable (hEx _).measurable,(hEx _).map_eq]

lemma compactRealLaw_diagonals (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).1≤1) ∧
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).2≤1) := by
  constructor
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).1.property.2)
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).2.property.2)

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_SynchronizedLimit
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

lemma source_contact_limit_exchangeable (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (ν : Measure _) (ν : Measure _) :=
  compact_exchangeability_limit hlim e (fun n => sourceGibbsArray_exchangeable
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) e)

end

lemma sourceLabelLaw_integral (k : ℕ) (w : Fin (k+1)→ℝ) (hw : ∀ l, 0≤w l)
    (g : unitInterval→ℝ) (hg : Measurable g) :
    (∫ x, g x ∂sourceLabelLaw k w)=∑ l, w l*g (sourceLabelLevel k l) := by
  unfold sourceLabelLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac' g _ hg.stronglyMeasurable,
      ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro l _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshGGLogUniqueness
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

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LabelFreshKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceLabelLevel_val_injective (k : ℕ) :
    Function.Injective (fun l : Fin (k+1) => (sourceLabelLevel k l).val) := by
  intro i j hij
  apply Fin.ext
  have h : (i.val:ℝ)=(j.val:ℝ) := by
    apply (div_left_inj' (show (k+1:ℕ)≠(0:ℝ) by positivity)).mp
    exact hij
  exact_mod_cast h

lemma labelProfileInterpolant_node {k : ℕ} (q : Fin (k+1)→ℝ) (l : Fin (k+1)) :
    labelProfileInterpolant q (sourceLabelLevel k l)=q l := by
  exact Lagrange.eval_interpolate_at_node q (sourceLabelLevel_val_injective k).injOn (Finset.mem_univ l)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReferenceValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileTerminal_lipschitz (g : Jet3) (s : ℝ≥0) :
    LipschitzWith (‖(g.heatLog s 1).d1‖₊*
      ‖innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))‖₊)
      (labelProfileTerminal g s) := by
  have he : labelProfileTerminal g s =
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog s 1).f
        ((innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))) v) := by
    funext v
    rw [Jet3.heatLog_f]
    rfl
  rw [he]
  have heatLipschitz : LipschitzWith ‖(g.heatLog s 1).d1‖₊ (g.heatLog s 1).f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun point => ((g.heatLog s 1).has1 point).differentiableAt)
    intro point
    rw [(g.heatLog s 1).deriv_eq]
    exact_mod_cast (g.heatLog s 1).d1.norm_coe_le_norm point
  exact heatLipschitz.comp
    (innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))).lipschitz

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
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma compactDiagonalMapBlock_continuous {e d : K→L} (he : Continuous e) (hd : Continuous d) (n : ℕ) :
    Continuous (compactDiagonalMapBlock e d n) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold compactDiagonalMapBlock
  split_ifs <;> fun_prop

omit [TopologicalSpace K] [TopologicalSpace L] in
lemma compactDiagonalMapBlock_compactBlock (e d : K→L) (n : ℕ) (Q : CompactArray K) :
    compactBlock n (compactDiagonalMapArray e d Q)=compactDiagonalMapBlock e d n (compactBlock n Q) := by
  funext i j
  simp only [compactBlock,compactDiagonalMapArray,compactDiagonalMapBlock,Fin.val_inj]


variable [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
  [SecondCountableTopology K] [SecondCountableTopology L]

lemma compactMapLaw_integral (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K))
    (F : CompactArray L→ℝ) (hF : Measurable F) :
    (∫ Q, F Q ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
      ∫ Q, F (compactMapArray e Q) ∂(μ : Measure (CompactArray K)) :=
  integral_map (compactMapArray_continuous he).measurable.aemeasurable hF.aestronglyMeasurable

lemma compactDiagonalMapLaw_integral (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K)) (F : CompactArray L→ℝ) (hF : Measurable F) :
    (∫ Q, F Q ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, F (compactDiagonalMapArray e d Q) ∂(μ : Measure (CompactArray K)) :=
  integral_map (compactDiagonalMapArray_continuous he hd).measurable.aemeasurable hF.aestronglyMeasurable

lemma compactDiagonalMapLaw_gg (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ),
      compactGGDefect μ n i f g=0) (n : ℕ) (i : Fin n)
    (f : CompactBlock L n →ᵇ ℝ) (g : L →ᵇ ℝ) :
    compactGGDefect (compactDiagonalMapLaw e d he hd μ) n i f g=0 := by
  let f' := f.compContinuous ⟨compactDiagonalMapBlock e d n,compactDiagonalMapBlock_continuous he hd n⟩
  let g' := g.compContinuous ⟨e,he⟩
  have hmul (a b : ℕ) (hab : a≠b) :
      (∫ Q, f (compactBlock n Q)*g (Q a b) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
        ∫ Q, f' (compactBlock n Q)*g' (Q a b) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => f (compactBlock n Q)*g (Q a b))
      ((f.measurable.comp (compactBlock_continuous n).measurable).mul (g.measurable.comp (by fun_prop)))]
    simp only [compactDiagonalMapBlock_compactBlock,compactDiagonalMapArray,ite_eq_right hab]
    rfl
  have hf : (∫ Q, f (compactBlock n Q) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, f' (compactBlock n Q) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => f (compactBlock n Q))
      (f.measurable.comp (compactBlock_continuous n).measurable)]
    simp only [compactDiagonalMapBlock_compactBlock]
    rfl
  have hg : (∫ Q, g (Q 0 1) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, g' (Q 0 1) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => g (Q 0 1)) (by fun_prop)]
    rfl
  unfold compactGGDefect
  rw [hmul i.val n (Nat.ne_of_lt i.isLt),hf,hg]
  have hs : (∑ j ∈ Finset.univ.erase i, ∫ Q, f (compactBlock n Q)*g (Q i j)
      ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∑ j ∈ Finset.univ.erase i, ∫ Q, f' (compactBlock n Q)*g' (Q i j)
        ∂(μ : Measure (CompactArray K)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply hmul
    intro hij
    exact (Finset.mem_erase.mp hj).1 (Fin.ext hij.symm)
  rw [hs]
  exact hGG n i f' g'
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compact_gg_spin_geometry (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hdiag : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ i, (Q i i).1.val=1) :
    ∀ᵐ Q ∂(μ : Measure _), CompactSpinGeometry Q := by
  have hg : ∀ᵐ Q ∂compactRealLaw μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)) :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst))).mpr hR
  have hu := scalarArray_ultrametric (compactRealLaw μ) (compactRealLaw_exchangeable μ hEx)
    (compactRealLaw_gg μ hGG) measurable_fst hg (compactRealLaw_diagonals μ).1
  have hbase : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      min (Q 0 1).1.val (Q 0 2).1.val ≤ (Q 1 2).1.val :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability)).mp hu
  have hdistinct (i j k : ℕ) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
      ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val := by
    let g : Fin 3 → ℕ := ![i,j,k]
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [g]
    obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (fun a : Fin 3 => a.val) g Fin.val_injective hg
    have h0 := he 0
    have h1 := he 1
    have h2 := he 2
    change e 0=i at h0
    change e 1=j at h1
    change e 2=k at h2
    have hh := (hEx e).quasiMeasurePreserving.ae hbase
    simpa only [compactRelabel,h0,h1,h2] using hh
  have hall : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      ∀ i j k, i≠j → i≠k → j≠k → min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val := by
    simp only [ae_all_iff]
    exact hdistinct
  filter_upwards [hR,hdiag,hall] with Q hQ hd hu
  have hs : ∀ i j, (Q i j).1.val=(Q j i).1.val :=
    gram_array_symmetric (fun i j => (Q i j).1.val) hQ
  refine ⟨hs,hd,?_⟩
  intro i j k
  by_cases hij : i=j
  · subst j
    exact min_le_right _ _
  by_cases hik : i=k
  · subst k
    rw [hs j i]
    exact min_le_left _ _
  by_cases hjk : j=k
  · subst k
    rw [hd j,min_self]
    exact (Q i j).1.property.2
  exact hu i j k hij hik hjk

lemma sourceGibbsArray_limit_spin_diagonal (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ i, (Q i i).1.val=1 := by
  rw [ae_all_iff]
  intro i
  have hc : IsClosed {Q : CompactArray CompactJointOverlap | (Q i i).1.val=1} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc
    (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
      hc (fun x => sourceJointArray_diagonal x i))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

lemma source_contact_limit_spin_geometry (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ → ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
    (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ) → Fin (n+1) → ℝ)
    (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k f (fun j => p j.val) (fun j => d j.val) (h n) z (t n) v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
    {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q := by
  apply compact_gg_spin_geometry ν
    (source_contact_limit_exchangeable k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)
    (source_contact_limit_joint_gg k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hs hlim hcover)
    (sourceGibbsArray_limit_gram k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim).1
    (sourceGibbsArray_limit_spin_diagonal k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem source_label_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0<w l) (hw1 : ∑ l,w l=1) (p d : ℕ→ℕ)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j,p j=a ∧ d j=b) :
    ∃ (u : (n : ℕ)→Fin (n+1)→ℝ)
      (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) (s : ℕ→ℕ),
      (∀ n,u n∈Icc (fun _=>1) (fun _=>2)) ∧ StrictMono s ∧
      Tendsto (fun n => sourceGibbsArrayLaw (s n) k 0 (fun j=>p j.val)
        (fun j=>d j.val) (fun _=>0) (u (s n)) (stepCumulative w) 0) atTop (𝓝 ν) ∧
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G g=0) ∧
      (∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e)
        (ν : Measure _) (ν : Measure _)) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2)=sourceLabelLaw k w ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) := by
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hc (n : ℕ) := source_perturbation_contact_exists n k (0 : ℝ →ᵇ ℝ)
    (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (fun _=>le_rfl) monotone_const
    (stepCumulative w) hz hz0 hz1 0
  choose u hu hm using hc
  obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence (fun n => sourceGibbsArrayLaw n k
    (0 : ℝ →ᵇ ℝ) (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (u n) (stepCumulative w) 0)
  refine ⟨u,ν,s,hu,hs,hlim,?_,?_,?_,?_⟩
  · exact source_contact_limit_joint_gg k 0 p d (stepCumulative w) hz hz0 hz1
      (fun _=>0) (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u hu hm
      (H:=0) (T:=0) le_rfl (fun _=>le_rfl) (fun _=>le_rfl) hs hlim hcover
  · exact source_contact_limit_exchangeable k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
      (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  · apply source_array_limit_label_law k 0 p d w hw hw1
      (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u (fun n j=>?_) (fun _=>0)
      (fun b hb=>hcover 0 b (by omega)) hs hlim
    have h := (hu n).1 j
    linarith
  · exact source_contact_limit_spin_geometry k 0 p d (stepCumulative w) hz hz0 hz1
      (fun _=>0) (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u hu hm
      (H:=0) (T:=0) le_rfl (fun _=>le_rfl) (fun _=>le_rfl) hcover hs hlim

lemma indexedCommonDepth_ultrametric (n : ℕ) (a b c : IndexedLeaf n) :
    min (indexedCommonDepth n a b) (indexedCommonDepth n a c)≤ indexedCommonDepth n b c := by
  let l := min (indexedCommonDepth n a b) (indexedCommonDepth n a c)
  apply (indexedLeafSharedVertex_eq_iff n b c l).mp
  exact ((indexedLeafSharedVertex_eq_iff n a b l).mpr (min_le_left _ _)).symm.trans
    ((indexedLeafSharedVertex_eq_iff n a c l).mpr (min_le_right _ _))

lemma sourceJointArray_label_geometry {N k : ℕ} (x : ℕ→NormalizedSpin N×IndexedLeaf k) :
    CompactLabelGeometry k (sourceJointArray x) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    simp only [sourceJointArray,sourceJointOverlap,indexedCommonDepth_comm k (x j).2 (x i).2]
  · intro i
    simp only [sourceJointArray,sourceJointOverlap,indexedCommonDepth_self,Fin.val_last]
  · intro i j l
    change min (((indexedCommonDepth k (x j).2 (x i).2).val:ℝ)/(k+1:ℕ))
      (((indexedCommonDepth k (x l).2 (x i).2).val:ℝ)/(k+1:ℕ))≤
      ((indexedCommonDepth k (x l).2 (x j).2).val:ℝ)/(k+1:ℕ)
    have h := indexedCommonDepth_ultrametric k (x i).2 (x j).2 (x l).2
    rw [indexedCommonDepth_comm k (x i).2 (x j).2,
      indexedCommonDepth_comm k (x i).2 (x l).2,indexedCommonDepth_comm k (x j).2 (x l).2] at h
    rcases le_total (indexedCommonDepth k (x j).2 (x i).2) (indexedCommonDepth k (x l).2 (x i).2) with he|he
    · rw [min_eq_left he] at h
      exact (min_le_left _ _).trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))
    · rw [min_eq_right he] at h
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))

lemma compactLabelGeometry_closed (k : ℕ) : IsClosed {Q | CompactLabelGeometry k Q} := by
  unfold CompactLabelGeometry
  simp only [ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
        isClosed_le (by fun_prop) (by fun_prop)))

lemma sourceGibbsArray_limit_label_geometry (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactLabelGeometry k Q := by
  have hc := compactLabelGeometry_closed k
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc (fun n=>sourceGibbsArray_closed_full
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) hc
    (fun x => sourceJointArray_label_geometry x))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compactLabelNodes_closed (k : ℕ) : IsClosed {Q | CompactLabelNodes k Q} := by
  unfold CompactLabelNodes
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (Set.finite_range (sourceLabelLevel k)).isClosed.preimage (by fun_prop)

lemma sourceGibbsArray_limit_label_nodes (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactLabelNodes k Q := by
  have hc := compactLabelNodes_closed k
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc (fun n=>sourceGibbsArray_closed_full
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) hc
    (fun x i j => ⟨indexedCommonDepth k (x j).2 (x i).2,rfl⟩))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

lemma labelProfileSpin_node {k : ℕ} (q : Fin (k+1)→Time) (l : Fin (k+1)) :
    labelProfileSpin q (sourceLabelLevel k l)=timeSpin (q l) := by
  apply Subtype.ext
  change min 1 (max 0 (labelProfileInterpolant (fun i => (q i:ℝ)) (sourceLabelLevel k l)))=(q l:ℝ)
  rw [labelProfileInterpolant_node,max_eq_right (q l).prop.1,min_eq_right (q l).prop.2]

lemma labelProfileMap_continuous {k : ℕ} (q : Fin (k+1)→Time) : Continuous (labelProfileMap q) :=
  ((labelProfileSpin_continuous q).comp continuous_snd).prodMk continuous_snd

lemma sourceLabelLevel_le {k : ℕ} (i j : Fin (k+1)) :
    sourceLabelLevel k i ≤ sourceLabelLevel k j ↔ i≤j := by
  change (i.val:ℝ)/(k+1:ℕ)≤(j.val:ℝ)/(k+1:ℕ) ↔ i≤j
  rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(k+1:ℕ))]
  exact_mod_cast (Iff.rfl : i.val≤j.val ↔ i≤j)

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReferenceFull
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

lemma labelProfileDiagonal_continuous : Continuous labelProfileDiagonal := by
  unfold labelProfileDiagonal
  fun_prop

lemma labelProfileSpin_ultra {k : ℕ} (q : Fin (k+1)→Time) (hq : Monotone q)
    {Q : CompactArray CompactJointOverlap} (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q)
    (i j l : ℕ) : min (labelProfileSpin q (Q i j).2).val (labelProfileSpin q (Q i l).2).val≤
      (labelProfileSpin q (Q j l).2).val := by
  obtain ⟨a,ha⟩ := hN i j
  obtain ⟨b,hb⟩ := hN i l
  obtain ⟨c,hc⟩ := hN j l
  have hs := hQ.2.2 i j l
  rw [←ha,←hb,←hc] at hs
  rw [←ha,←hb,←hc,labelProfileSpin_node,labelProfileSpin_node,labelProfileSpin_node]
  change min (q a:ℝ) (q b:ℝ)≤(q c:ℝ)
  rcases le_total a b with hab|hab
  · have hab' : (sourceLabelLevel k a).val ≤ (sourceLabelLevel k b).val :=
      (sourceLabelLevel_le a b).mpr hab
    have hac : a ≤ c := (sourceLabelLevel_le a c).mp (by
      change (sourceLabelLevel k a).val≤(sourceLabelLevel k c).val
      simpa only [min_eq_left hab'] using hs)
    exact (min_le_left _ _).trans (hq hac)
  · have hba' : (sourceLabelLevel k b).val ≤ (sourceLabelLevel k a).val :=
      (sourceLabelLevel_le b a).mpr hab
    have hbc : b ≤ c := (sourceLabelLevel_le b c).mp (by
      change (sourceLabelLevel k b).val≤(sourceLabelLevel k c).val
      simpa only [min_eq_right hba'] using hs)
    exact (min_le_right _ _).trans (hq hbc)

lemma labelProfileDiagonalMap_geometry {k : ℕ} (q : Fin (k+1)→Time) (hq : Monotone q)
    {Q : CompactArray CompactJointOverlap} (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q) :
    CompactSpinGeometry (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q) := by
  have hsym (i j : ℕ) : (Q i j).2=(Q j i).2 := Subtype.ext (hQ.1 i j)
  refine ⟨?_,?_,?_⟩
  · intro i j
    by_cases hij : i=j
    · subst j; rfl
    · simp only [compactDiagonalMapArray,ite_eq_right hij,ite_eq_right (Ne.symm hij),labelProfileMap,hsym i j]
  · intro i
    simp only [compactDiagonalMapArray,↓reduceIte,labelProfileDiagonal]
  · intro i j l
    by_cases hjl : j=l
    · subst l
      simp only [compactDiagonalMapArray,↓reduceIte,labelProfileDiagonal,min_self]
      split_ifs <;> first | exact le_rfl | exact (labelProfileSpin q (Q i j).2).prop.2
    · by_cases hij : i=j
      · subst j
        simp only [compactDiagonalMapArray,↓reduceIte,ite_eq_right hjl,labelProfileDiagonal,labelProfileMap]
        exact min_le_right _ _
      · by_cases hil : i=l
        · subst l
          simp only [compactDiagonalMapArray,↓reduceIte,ite_eq_right hij,ite_eq_right hjl,labelProfileDiagonal,labelProfileMap]
          rw [hsym i j]
          exact min_le_left _ _
        · simp only [compactDiagonalMapArray,ite_eq_right hij,ite_eq_right hil,ite_eq_right hjl,labelProfileMap]
          exact labelProfileSpin_ultra q hq hQ hN i j l

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedVisitKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma tiltedMarkKernel_markov (ν : ProbabilityMeasure S) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedMarkKernel ν z F) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [tiltedMarkKernel,Kernel.withDensity_apply _ ((hF.const_mul z).exp.ennreal_ofReal)]
  simp only [Kernel.const_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI x)
    (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)),hM x]
  exact ENNReal.ofReal_one

lemma tiltedStateStep_markov (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedStateStep ν step z F) := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  exact Kernel.IsMarkovKernel.map _ hs

lemma pathOneKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) : IsMarkovKernel (pathOneKernel n κ) := by
  induction n with
  | zero => dsimp [pathOneKernel]; infer_instance
  | succ n ih =>
    have := hκ 0
    have := ih (fun i => κ i.succ) (fun i => hκ i.succ)
    dsimp [pathOneKernel]; infer_instance

lemma pathMean_bound (n : ℕ) (κ : Fin n → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (C : ℝ) (hb : ∀ x, |f x| ≤ C) (x : X) : |pathMean n κ f x| ≤ C := by
  have := pathOneKernel_markov n κ hκ
  simpa [pathMean] using norm_integral_le_of_norm_le_const
    (μ := pathOneKernel n κ x) (f := f)
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedTerminalProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma cascadeTiltedStep_markov (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (i : Fin n) :
    IsMarkovKernel (tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) :=
  tiltedStateStep_markov ν step hs (z i) _ (finiteCascadeShifts_measurable ν step hs n z hH i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedPathDiagonal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
variable {X Y R Q : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q]

open scoped ENNReal NNReal BoundedContinuousFunction

lemma residualResponse_eq_tiltMean (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    residualResponse s f v x =
      tiltMean (gaussianReal 0 s) (fun z => f (x+z)) (fun z => v (x+z)) 1 := by
  simp only [residualResponse,gaussianAverage,tiltMean,tiltIntegral,tiltPartition,
    Pi.mul_apply,expBCF_apply,one_mul]

lemma residualResponse_bound (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    |residualResponse s f v x|≤‖v‖ := by
  rw [residualResponse_eq_tiltMean]
  exact tilt_mean_bound (gaussianReal 0 s) (f.measurable.comp (measurable_const.add measurable_id))
    (v.measurable.comp (measurable_const.add measurable_id)) (norm_nonneg _) (norm_nonneg _)
    (fun z => f.norm_coe_le_norm (x+z)) (fun z => v.norm_coe_le_norm (x+z)) 1

lemma residualResponse_one (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    residualResponse s f 1 x=1 := by
  change gaussianAverage s (expBCF 1 f * 1 : ℝ →ᵇ ℝ) x / _=1
  rw [mul_one]
  exact div_self (gaussianAverage_exp_pos s 1 f x).ne'

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationPair
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelResidualObservable_bound (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    |labelResidualObservable s f v x|≤‖v‖ := residualResponse_bound s f v _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelPairTestValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma labelMarkedBlockKernel_profile {k r : ℕ} (q : Fin (k+1)→Time)
    (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (Q : CompactBlock CompactJointOverlap r)
    (hN : ∀ i l,(Q i l).2∈Set.range (sourceLabelLevel k)) :
    labelMarkedBlockKernel (fun i => (q i:ℝ)) Ψ Q = freshMarkedMatrixKernel Ψ (labelProfileGram q Q) := by
  apply congrArg (freshMarkedMatrixKernel Ψ)
  funext i l
  change (if i=l then 1 else labelProfileInterpolant (fun i => (q i:ℝ)) (Q i l).2)=_
  by_cases hil : i=l
  · simp only [hil,labelProfileGram,ite_true]
  · obtain ⟨d,hd⟩ := hN i l
    simp only [labelProfileGram,ite_eq_right hil,←hd,labelProfileInterpolant_node,labelProfileSpin_node,timeSpin]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkLimitGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelSingleRestoredValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction Topology

lemma singleRestorationBound_nonneg (f v w : ℝ →ᵇ ℝ) : 0≤ singleRestorationBound f v w := by
  unfold singleRestorationBound; positivity

lemma restorationBlockTest_one (r j : ℕ) :
    restorationBlockTest r 1 j=(1 : CompactBlock CompactOverlap (r+j) →ᵇ ℝ) := by
  induction j with
  | zero => rfl
  | succ j hj => ext Q; change restorationBlockTest r 1 j _=1; rw [hj]; rfl

lemma jointRestorationBlockTest_one (r j : ℕ) :
    jointRestorationBlockTest r 1 j=(1 : CompactBlock CompactJointOverlap (r+j) →ᵇ ℝ) := by
  induction j with
  | zero => rfl
  | succ j hj => ext Q; change jointRestorationBlockTest r 1 j _=1; rw [hj]; rfl

lemma scalarRestorationSingleMoment_compact (f v w : ℝ →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactOverlap (1+j)) :
    scalarRestorationSingleMoment f v w j (fun i l => (Q i l).val) =
      (restorationBlockTest 1 1 j *
        freshMarkedCompactBlockKernel (restorationMarkTest 1 f (gaussianMixedTest (fun _ => v)) j) *
        freshMarkedCompactBlockKernel (restorationMarkTest 1 f (gaussianMixedTest (fun _ => w)) j)) Q := by
  simp only [restorationBlockTest_one,one_mul,scalarRestorationSingleMoment,
    BoundedContinuousFunction.mul_apply,restorationMarkTest_gaussianMixed]
  rfl

lemma scalarRestorationSingleMoment_label {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (j : ℕ)
    (Q : CompactBlock CompactJointOverlap (1+j))
    (hN : ∀ i l,(Q i l).2∈Set.range (sourceLabelLevel k)) :
    scalarRestorationSingleMoment f v w j (labelProfileGram q Q) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ : Fin 1 => v) (fun _ => w)
        1 j Q := by
  simp only [scalarRestorationSingleMoment,labelRestorationBlockMoment,BoundedContinuousFunction.mul_apply,
    jointRestorationBlockTest_one,one_mul,
    labelMarkedBlockKernel_profile q _ Q hN]

lemma scalarRestorationSingleMoment_diagonalMap {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (j : ℕ)
    (Q : CompactArray CompactJointOverlap) (hN : CompactLabelNodes k Q) :
    scalarRestorationSingleMoment f v w j (fun i l =>
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ : Fin 1 => v) (fun _ => w)
        1 j (compactBlock (1+j) Q) := by
  have he : (fun i l : Fin (1+j) => (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val)=
      labelProfileGram q (compactBlock (1+j) Q) := by
    funext i l
    simp only [compactDiagonalMapArray,labelProfileGram,Fin.val_inj]
    split_ifs <;> rfl
  rw [he]
  exact scalarRestorationSingleMoment_label q f v w j _ (fun i l => hN i l)

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

lemma roundTime_sum_integral (q : BoundedField 1) (n : ℕ) (F : CompactOverlap→ᵇℝ) :
    (∑ i,(strictRoundModel q n).weight i*F (timeSpin (roundTimeValue q n i)))=
      ∫ u,F (timeSpin (roundTime q n u)) ∂timeLaw := by
  have he := integral_finite_label (strictRoundModel q n).label (strictRoundModel q n).measurable_label
    (fun i => F (timeSpin (roundTimeValue q n i)))
  simp only [FiniteFieldModel.weight]
  rw [←he]
  apply integral_congr_ae
  filter_upwards [(strictRoundModel q n).agrees] with u hu
  exact congrArg (fun t => F (timeSpin t)) (Subtype.ext hu)

lemma roundTime_sum_tendsto (q : Time→Time) (hq : Monotone q) (F : CompactOverlap→ᵇℝ) :
    Tendsto (fun n => ∑ i,(strictRoundModel (unitQuantileField q hq) n).weight i*
      F (timeSpin (roundTimeValue (unitQuantileField q hq) n i))) atTop
      (𝓝 (∫ u,F (timeSpin (q u)) ∂timeLaw)) := by
  simp_rw [roundTime_sum_integral]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.measurable.comp (timeSpin_continuous.measurable.comp (roundTime_mono _ _).measurable)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun u => F.norm_coe_le_norm _
  · exact ae_of_all _ fun u =>
      (((F.continuous.comp timeSpin_continuous).tendsto _).comp (roundTime_tendsto q hq u))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileSingleReference
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

theorem labelProfile_single_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (q : Fin (k+1)→Time) (hq : Monotone q)
    (g : Jet3) (v v' : ℝ →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ A : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*A (timeSpin (q l))) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v v' j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 1 x.2 ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=
        labelSingleCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
          (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v *
        labelSingleCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
          (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v'  := by
  let p := fun n => (Nat.unpair n).1
  let d := fun n => (Nat.unpair n).2
  have hcover : ∀ a b : ℕ, 1≤a+b → ∃ j,p j=a ∧ d j=b := by
    intro a b _
    exact ⟨Nat.pair a b,by simp [p,d]⟩
  obtain ⟨u,ρ,s,hu,hs,hlim,hGG,hex,hpair,hgeo⟩ := source_label_reference_exists k w hw hw1 p d hcover
  have hL := sourceGibbsArray_limit_label_geometry k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  have hN := sourceGibbsArray_limit_label_nodes k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  let ν := compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
  obtain ⟨η,hm,hl⟩ := sourceLabelSingle_witness k q hq 0 g v v'
    (fun _ j=>p j.val) (fun _ j=>d j.val) (fun _ _=>0) (fun _ _=>le_rfl)
    (fun _=>monotone_const) u (stepCumulative w) (stepCumulative_strictMono w hw)
    (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1) (fun _=>0) s hlim
  refine ⟨ν,η,compactDiagonalMapLaw_gg _ _ _ _ ρ hGG,?_,?_,?_,?_⟩
  · change ∀ᵐ Q ∂(ρ : Measure (CompactArray CompactJointOverlap)).map
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal), CompactSpinGeometry Q
    apply (ae_map_iff (compactDiagonalMapArray_continuous (labelProfileMap_continuous q) labelProfileDiagonal_continuous).measurable.aemeasurable
      compactSpinGeometry_closed.measurableSet).mpr
    filter_upwards [hL,hN] with Q hLQ hNQ
    exact labelProfileDiagonalMap_geometry q hq hLQ hNQ
  · intro A
    change (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _))=_
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => A (Q 0 1).1) (by fun_prop)]
    have he : (∫ Q, A (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=
        ∫ Q, A (labelProfileSpin q (Q 1 0).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)) := by
      apply integral_congr_ae
      filter_upwards [hL] with Q hLQ
      rw [show (Q 0 1).2=(Q 1 0).2 from Subtype.ext (hLQ.1 0 1)]
    change (∫ Q, A (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=_
    have hmap : (∫ x, A (labelProfileSpin q x) ∂((ρ : Measure (CompactArray CompactJointOverlap)).map
        (fun Q => (Q 1 0).2)))=∫ Q, A (labelProfileSpin q (Q 1 0).2)
          ∂(ρ : Measure (CompactArray CompactJointOverlap)) :=
      integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 1 0).2)
        from by fun_prop).aemeasurable
        (show Measurable (fun x : Time => A (labelProfileSpin q x)) from
          A.measurable.comp (labelProfileSpin_continuous q).measurable).aestronglyMeasurable
    rw [he,←hmap,hpair,sourceLabelLaw_integral k w (fun l => (hw l).le) (fun x => A (labelProfileSpin q x))
      (A.measurable.comp (labelProfileSpin_continuous q).measurable)]
    simp_rw [labelProfileSpin_node]
  · intro j
    rw [hm j]
    change _=∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v v' j (fun i l => (Q i l).1.val)
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal
        (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _)
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal
      (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => scalarRestorationSingleMoment g.f v v' j (fun i l => (Q i l).1.val))
      ((scalarRestorationSingleMoment g.f v v' j).continuous.comp (by fun_prop)).measurable]
    apply integral_congr_ae
    filter_upwards [hN] with Q hNQ
    exact (scalarRestorationSingleMoment_diagonalMap q g.f v v' j Q hNQ).symm
  · exact hl

lemma rootPathMean_bound {X R : Type} [MeasurableSpace X] [MeasurableSpace R]
    (μ : Measure R) [IsProbabilityMeasure μ] (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X→ℝ) (C : ℝ) (hb : ∀ y,|f y|≤C) :
    |rootPathMean μ x n κ f|≤C := by
  simpa only [rootPathMean,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=μ)
      (f:=fun r => pathMean n κ f (x r))
      (ae_of_all _ fun r => by simpa only [Real.norm_eq_abs] using pathMean_bound n κ hκ f C hb (x r))

lemma labelSingleCoefficient_bound (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v : ℝ →ᵇ ℝ) :
    |labelSingleCoefficient k z q g s v|≤‖v‖ := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (labelGaussianStep q) (labelProfileTerminal_lipschitz g s) k z hz0
  have hκ i := cascadeTiltedStep_markov (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (gaussianLinearMarkStep (labelGaussianStep q)) (gaussianLinearMarkStep_measurable _)
    k z hz0 (fun x => labelProfileTerminal g s (x 0))
    ((labelProfileTerminal_lipschitz g s).continuous.measurable.comp (measurable_pi_apply 0)) hI.2 i
  exact rootPathMean_bound (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (fun r => fun _ => labelGaussianRoot q r) k _ hκ
    (fun x => labelResidualObservable s g.f v (x 0)) ‖v‖
    (fun x => labelResidualObservable_bound s g.f v (x 0))

lemma labelSingleCoefficient_one (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) :
    labelSingleCoefficient k z q g s 1=1 := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (labelGaussianStep q) (labelProfileTerminal_lipschitz g s) k z hz0
  have hκ i := cascadeTiltedStep_markov (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (gaussianLinearMarkStep (labelGaussianStep q)) (gaussianLinearMarkStep_measurable _)
    k z hz0 (fun x => labelProfileTerminal g s (x 0))
    ((labelProfileTerminal_lipschitz g s).continuous.measurable.comp (measurable_pi_apply 0)) hI.2 i
  have := pathOneKernel_markov k _ hκ
  simp only [labelSingleCoefficient,rootPathMean,labelResidualObservable,residualResponse_one,pathMean,
    integral_const,probReal_univ,one_smul]

lemma roundedSingleCoeff_bound (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) :
    |roundedSingleCoeff q n g v|≤‖v‖ :=
  labelSingleCoefficient_bound _ _ (stepCumulative_pos _ (strictRoundModel q n).weight_pos) _ _ _ _

lemma roundedSingleCoeff_one (q : BoundedField 1) (n : ℕ) (g : Jet3) :
    roundedSingleCoeff q n g 1=1 :=
  labelSingleCoefficient_one _ _ (stepCumulative_pos _ (strictRoundModel q n).weight_pos) _ _ _

theorem rounded_single_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (v v' : ℝ→ᵇℝ)  (b : ℕ→ℕ) (hb : StrictMono b)
    (L : ℝ) (hL : Tendsto (fun n =>
      roundedSingleCoeff (unitQuantileField q hq) (b n) g v *
      roundedSingleCoeff (unitQuantileField q hq) (b n) g v') atTop (𝓝 L)) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v v' j
          (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 1 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=L := by
  have hex (n : ℕ) := labelProfile_single_reference_exists
    (strictRoundModel (unitQuantileField q hq) (b n)).depth
    (strictRoundModel (unitQuantileField q hq) (b n)).weight
    (strictRoundModel (unitQuantileField q hq) (b n)).weight_pos
    (strictRoundModel (unitQuantileField q hq) (b n)).weight_sum
    (roundTimeValue (unitQuantileField q hq) (b n)) (roundTimeValue_mono _ _) g v v'
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
      (Measure.isProbabilityMeasure_map_iff (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable).2 inferInstance⟩
    have he : ρ=quantileSpinLaw q hq.measurable := by
      apply probability_Icc_eq_of_moments
      intro r
      rw [quantileSpinLaw_integral q hq.measurable (fun x => x.val^r) (by fun_prop)]
      change (∫ x : CompactOverlap, x.val^r ∂(ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))=_
      rw [integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable (show Measurable (fun x : CompactOverlap => x.val^r) from by fun_prop).aestronglyMeasurable]
      let A : CompactOverlap→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x=>x.val^r,by fun_prop⟩
      let B : CompactArray CompactJointOverlap→ᵇℝ := A.compContinuous ⟨fun Q => (Q 0 1).1,by fun_prop⟩
      have hν := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hlim
      change Tendsto (fun n => ∫ Q, A (Q 0 1).1 ∂(μ (s n) : Measure (CompactArray CompactJointOverlap))) atTop
        (𝓝 (∫ Q, (Q 0 1).1.val^r ∂(ν : Measure (CompactArray CompactJointOverlap)))) at hν
      simp_rw [hpair] at hν
      exact tendsto_nhds_unique hν
        ((roundTime_sum_tendsto q hq A).comp (hb.comp hs).tendsto_atTop)
    exact congrArg (fun x : ProbabilityMeasure CompactOverlap => (x : Measure CompactOverlap)) he
  obtain ⟨η,-,t,ht,hη⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (ξ (s n)))
  have hv := hlim.comp ht.tendsto_atTop
  refine ⟨ν,η,hG,hgeom,hp,?_,?_⟩
  · intro j
    let A : WeightedRestorationRange g.f (singleRestorationBound g.f v v') →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*x.2.val^j,by fun_prop⟩
    let B : CompactArray CompactJointOverlap →ᵇ ℝ :=
      (scalarRestorationSingleMoment g.f v v' j).compContinuous
        ⟨fun Q i l => (Q i l).1.val,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hv
    change Tendsto (fun n => ∫ x,x.1.val*x.2.val^j ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v')))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))) at h₁
    simp_rw [hm] at h₁
    exact tendsto_nhds_unique h₁ h₂
  · let A : WeightedRestorationRange g.f (singleRestorationBound g.f v v') →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*restorationReciprocal g.f 1 x.2,
        (continuous_subtype_val.comp continuous_fst).mul
          ((restorationReciprocal g.f 1).continuous.comp continuous_snd)⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    change Tendsto (fun n => ∫ x,x.1.val*restorationReciprocal g.f 1 x.2 ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v')))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 1 x.2 ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))) at h₁
    simp_rw [hl] at h₁
    exact tendsto_nhds_unique h₁ (hL.comp (hs.comp ht).tendsto_atTop)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileSingleReference
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

theorem quantile_single_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (v : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖v‖ ∧ ∀ b : Bool,
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v (secondPairMark v b)))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v (secondPairMark v b)))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v (secondPairMark v b) j
          (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 1 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v (secondPairMark v b)))))=
          c^(pairMarkPower b) := by
  let a : ℕ→ℝ := fun n => roundedSingleCoeff (unitQuantileField q hq) n g v
  have hb (n : ℕ) : a n∈Icc (-‖v‖) ‖v‖ := abs_le.mp (roundedSingleCoeff_bound _ _ _ _)
  obtain ⟨c,hc,s,hs,ht⟩ := isCompact_Icc.isSeqCompact hb
  change Tendsto (fun n => roundedSingleCoeff (unitQuantileField q hq) (s n) g v) atTop (𝓝 c) at ht
  refine ⟨c,abs_le.mpr hc,fun b => ?_⟩
  apply rounded_single_reference_exists q hq g v (secondPairMark v b) s hs
  cases b
  · simpa only [a,Function.comp_apply,secondPairMark,pairMarkPower,Bool.false_eq_true,ite_false,roundedSingleCoeff_one,
      pow_one,mul_one] using ht
  · simpa only [a,Function.comp_apply,secondPairMark,pairMarkPower,ite_true,pow_two] using ht.mul ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma bulk_single_ratio_tendsto_of_reference (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (w w' : ℝ→ᵇℝ)
    (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f w w')))
    (hm : ∀ j,(∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w'))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationSingleMoment g.f w w' j
        (fun i l => (Q i l).val) ∂(ν : Measure _)) :
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 1 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w'))))) := by
  let Ψ : EuclideanSpace ℝ (Fin 1) →ᵇ ℝ := gaussianMixedTest (fun _ => w)
  let Φ : EuclideanSpace ℝ (Fin 1) →ᵇ ℝ := gaussianMixedTest (fun _ => w')
  let C := ‖(1 : CompactBlock CompactOverlap 1 →ᵇ ℝ)‖*‖restorationMarkTest 1 g.f Ψ 0‖*‖restorationMarkTest 1 g.f Φ 0‖+
    singleRestorationBound g.f w w'
  have hC : 0≤C := add_nonneg (by positivity) (singleRestorationBound_nonneg _ _ _)
  have hηB (x : WeightedRestorationRange g.f (singleRestorationBound g.f w w')) : |x.1.val|≤C :=
    (abs_le.mpr x.1.prop).trans (le_add_of_nonneg_left (by positivity))
  have hb (n : ℕ) (p : TwoFreshDisorder (s n+1) (M (s n))) :
      |bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n)) 1 Ψ Φ p|≤C :=
    (bulkFreshNumerator_bound _ _ _ _ _ _ _ _ _).trans
      (le_add_of_nonneg_right (singleRestorationBound_nonneg _ _ _))
  have hmoment j : Tendsto (fun n => ∫ p,
      bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n)) 1 Ψ Φ p *
      (bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n)) p).val^j
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w'))))) := by
    rw [hm j]
    simp_rw [scalarRestorationSingleMoment_compact]
    exact bulkFresh_moment_tendsto M g.f v s hlim 1 1 Ψ Φ j
  have ht := restoration_ratio_tendsto
    (fun n => twoFreshDisorderLaw (s n+1) (M (s n)))
    (η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w')))
    (Real.exp_pos _)
    (fun n => bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n)) 1 Ψ Φ)
    (fun x => x.1.val)
    (fun n => bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n))) (fun x => x.2)
    (fun n => bulkFreshNumerator_measurable _ _ _ _ _ _ _ _) (by fun_prop)
    (fun n => bulkFreshCompactDenominator_measurable _ _ _ _) (by fun_prop)
    hC hb hηB hmoment 1
  simpa only [div_eq_mul_inv, restorationReciprocal, ContinuousMap.coe_mk, bulkFreshCompactDenominator, Ψ, Φ] using ht

theorem bulk_single_limit_exists_oai (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧ ∀ b : Bool,
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>secondPairMark w b)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 (c^(pairMarkPower b))) := by
  let q := boundedQuantile ((compactPositivePairLaw (bulkJointLaw ν)).map Prod.fst)
  have hq : Monotone q := boundedQuantile_monotone _
  obtain ⟨c,hc,href⟩ := quantile_single_reference_exists q hq g w
  refine ⟨c,hc,fun b => ?_⟩
  obtain ⟨ρ,η,hG,hge,hp,hm,hl⟩ := href b
  have hpair := (compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn).trans hp.symm
  have he (j : ℕ) : (∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w (secondPairMark w b)))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationSingleMoment g.f w (secondPairMark w b) j
        (fun i l => (Q i l).val) ∂(ν : Measure _) := by
    rw [hm j,←scalarGram_eq_of_pair_law (bulkJointLaw ν) ρ hGG hG hgeo hge hpair]
    exact bulkJointLaw_scalarGram_integral ν _ _
  have ht := bulk_single_ratio_tendsto_of_reference M g v s hlim w (secondPairMark w b) η he
  rwa [hl] at ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists_oai := @OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists_oai
