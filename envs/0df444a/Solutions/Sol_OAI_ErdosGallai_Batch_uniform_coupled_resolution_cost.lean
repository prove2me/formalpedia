-- Prove2me | solution 1 for OAI.ErdosGallai.Batch.uniform_coupled_resolution_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:06:12.035431+00:00
-- url     : https://prove2.me/submissions/706b0c6f-b2a1-418b-9698-62454aa27334

import Mathlib
import Definitions.Def_CycleDecomposition
import Definitions.Def_OAIQWEGC000
import Theorems.Thm_OAI_ErdosGallai_lovasz_path_cycle_decomposition

section
-- module Solutions.OAIQW_ErdosGallai.Compat
namespace OAI.ErdosGallai
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434


end OAI.ErdosGallai
end

section
-- module Solutions.OAIQW_ErdosGallai.EdgeSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Splitting
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

lemma colorIndicator_indep {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) :
    iIndepFun (colorIndicator (V := V) i) (edgeColorMeasure V l) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma colorIndicator_integral {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) (e : Sym2 V) :
    ∫ ω, colorIndicator i e ω ∂edgeColorMeasure V l = 1/(l : ℝ) := by
  have hl := (measurePreserving_eval
    (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
  have hi := hl.integral_comp (f := fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [PMF.integral_eq_sum] at hi
  simpa [edgeColorMeasure, colorIndicator, PMF.uniformOfFintype_apply] using hi

lemma colorGraph_interedges {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S T : Finset V) :
    (colorGraph P ω i).interedges S T =
      (P.interedges S T).filter (fun e => ω s(e.1,e.2) = i) := by
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_filter]
  change (x ∈ S ∧ y ∈ T ∧ (P.Adj x y ∧ ω s(x,y) = i)) ↔ _
  tauto

lemma color_cut_sum (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S : Finset V) :
    (∑ e ∈ (P.interedges S Sᶜ).image (fun e => s(e.1,e.2)), colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
  rw [Finset.sum_image (boundary_sym2_injective P S)]
  simp only [colorIndicator, Finset.sum_boole, colorGraph_interedges]

lemma color_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] (i : Fin l) (S : Finset V) {h : ℝ}
    (hexp : CutExpansion P h) (hS : S.card ≤ Sᶜ.card) :
    (edgeColorMeasure V l).real {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ≤
        exp (-h*S.card/(8*l)) := by
  let E := (P.interedges S Sᶜ).image (fun e => s(e.1,e.2))
  have hcard : E.card = (P.interedges S Sᶜ).card :=
    Finset.card_image_of_injOn (boundary_sym2_injective P S)
  have hl : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  have hcut : h * S.card ≤ (E.card : ℝ) := by
    rw [hcard]
    have he := hexp S
    rwa [min_eq_left (by exact_mod_cast hS)] at he
  have hb := bernoulli_sum_lower_tail (μ := edgeColorMeasure V l) E
    (fun e => measurable_of_finite (colorIndicator i e)) (colorIndicator_indep i)
    (fun e ω => by simp only [colorIndicator]; split <;> simp)
    (1/(l : ℝ)) (by positivity) (colorIndicator_integral i)
  apply (measureReal_mono (show {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ⊆
      {ω | (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2} from ?_)).trans
      (hb.trans ?_)
  · intro ω hω
    change (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2
    rw [show (∑ e ∈ E, colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) from color_cut_sum P ω i S]
    calc
      _ ≤ h*S.card/(2*l) := le_of_lt hω
      _ ≤ (E.card : ℝ)/(2*l) := div_le_div_of_nonneg_right hcut (by positivity)
      _ = _ := by ring
  · apply exp_le_exp.mpr
    have he := div_le_div_of_nonneg_right hcut (show 0 ≤ 8*(l : ℝ) by positivity)
    calc
      _ = -((E.card : ℝ)/(8*l)) := by ring
      _ ≤ -(h*S.card/(8*l)) := neg_le_neg he
      _ = _ := by ring

lemma cutExpansion_of_small_cuts (P : SimpleGraph V) [DecidableRel P.Adj] {h : ℝ}
    (hcut : ∀ S : Finset V, S.Nonempty → S.card ≤ Sᶜ.card →
      h*S.card ≤ ((P.interedges S Sᶜ).card : ℝ)) : CutExpansion P h := by
  intro S
  by_cases he : S = ∅
  · simp [he]
  by_cases hc : Sᶜ = ∅
  · simp [hc]
  by_cases hs : S.card ≤ Sᶜ.card
  · rw [min_eq_left (by exact_mod_cast hs)]
    exact hcut S (Finset.nonempty_iff_ne_empty.mpr he) hs
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
    have hi := hcut Sᶜ (Finset.nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs)
    have hcomm : (P.interedges Sᶜ S).card = (P.interedges S Sᶜ).card := by
      have := P.symm
      exact Rel.card_interedges_comm Sᶜ S
    simpa only [compl_compl, hcomm] using hi

lemma sum_nonempty_subsets_power (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)).erase ∅, q^S.card) =
      (1+q)^(Fintype.card V)-1 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun S : Finset V => q^S.card)
    (Finset.mem_univ (∅ : Finset V))
  have hp := Finset.prod_one_add (s := (Finset.univ : Finset V)) (f := fun _ => q)
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at hp
  simp only [Finset.card_empty, pow_zero] at hs
  linarith

theorem edge_splitting_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h) :
    (edgeColorMeasure V l).real {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ≤
      l * (exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) := by
  let cuts : Finset (Finset V) := Finset.univ.erase ∅
  let B (i : Fin l) (S : Finset V) : Set (Sym2 V → Fin l) :=
    {ω | S.card ≤ Sᶜ.card ∧
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)}
  let q : ℝ := exp (-h/(8*l))
  have cover : {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S := by
    intro ω hω
    rcases hω with ⟨i, hi⟩
    by_contra hn
    apply hi
    apply cutExpansion_of_small_cuts
    intro S hS hs
    have hb : ω ∉ B i S := by
      intro hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hS.ne_empty, Finset.mem_univ _⟩, hm⟩⟩⟩⟩
    have hc : h*S.card/(2*l) ≤ (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
      exact le_of_not_gt (fun hf => hb ⟨hs, hf⟩)
    convert hc using 1 ; ring
  have hbound (i : Fin l) (S : Finset V) :
      (edgeColorMeasure V l).real (B i S) ≤ q^S.card := by
    by_cases hs : S.card ≤ Sᶜ.card
    · calc
        _ ≤ (edgeColorMeasure V l).real {ω |
            (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} :=
          measureReal_mono (fun _ hw => hw.2)
        _ ≤ exp (-h*S.card/(8*l)) := color_cut_lower_tail P i S hexp hs
        _ = q^S.card := by dsimp [q]; rw [← exp_nat_mul]; congr 1; ring
    · have he : B i S = ∅ := by ext ω; simp [B,hs]
      rw [he, measureReal_empty]
      exact pow_nonneg (exp_pos _).le _
  calc
    _ ≤ (edgeColorMeasure V l).real
        (⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S) :=
      measureReal_mono cover (measure_ne_top _ _)
    _ ≤ ∑ i : Fin l, (edgeColorMeasure V l).real (⋃ S ∈ cuts, B i S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i : Fin l, ∑ S ∈ cuts, (edgeColorMeasure V l).real (B i S) :=
      Finset.sum_le_sum (fun _ _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _i : Fin l, ∑ S ∈ cuts, q^S.card := by
      apply Finset.sum_le_sum; intro i _; exact Finset.sum_le_sum (fun S _ => hbound i S)
    _ = (l : ℝ)*((1+q)^(Fintype.card V)-1) := by
      simp only [cuts, sum_nonempty_subsets_power, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ l*(exp ((Fintype.card V : ℝ)*q)-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg l)
      apply sub_le_sub_right
      calc
        _ ≤ (exp q)^(Fintype.card V) :=
          pow_le_pow_left₀ (by dsimp [q]; positivity) (by linarith [add_one_le_exp q]) _
        _ = _ := (exp_nat_mul _ _).symm

theorem edge_splitting_of_error_lt_one (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h)
    (herror : (l : ℝ)*(exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) < 1) :
    ∃ ω : Sym2 V → Fin l,
      (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
      (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
      (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have he := (edge_splitting_failure_bound P hexp).trans_lt herror
  have hh : ∃ ω : Sym2 V → Fin l, ∀ i, CutExpansion (colorGraph P ω i) (h/(2*l)) := by
    by_contra hn
    push Not at hn
    have hall : {ω : Sym2 V → Fin l | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} =
        Set.univ := Set.eq_univ_of_forall hn
    simp only [hall, Measure.real, measure_univ, ENNReal.toReal_one] at he
    exact (lt_irrefl _ he)
  obtain ⟨ω, hω⟩ := hh
  refine ⟨ω, hω, ?_, ?_⟩
  · intro x y
    exact ⟨fun hxy => ⟨ω s(x,y), hxy, rfl⟩, fun ⟨_, hxy, _⟩ => hxy⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with | _ x y =>
      have hi : (colorGraph P ω i).Adj x y := by simpa using hei
      have hj : (colorGraph P ω j).Adj x y := by simpa using hej
      exact hij (hi.2.symm.trans hj.2)

end

open Filter Asymptotics
open scoped Topology

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

lemma edgeSplittingScaleError_tendsto (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    Tendsto (edgeSplittingScaleError c l) atTop (𝓝 0) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have ht := tendsto_monomial_exp_neg_power (51/50) (9/10) (c/(8*l))
    (by norm_num) (by positivity)
  have hh := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l : ℝ)
  unfold edgeSplittingScaleError
  convert hh using 1 <;> norm_num

universe u

theorem edge_splitting_uniform (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ),
      c*D^(9/10 : ℝ) ≤ h → D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) → CutExpansion P h →
      ∃ ω : Sym2 V → Fin l,
        (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
        (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
        (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have : NeZero l := ⟨hl.ne'⟩
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hevent := (edgeSplittingScaleError_tendsto c hc l hl).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ h hh _hrlo hrhi hexp
  apply edge_splitting_of_error_lt_one P hexp
  apply lt_of_le_of_lt _ (hD₀ D hD)
  unfold edgeSplittingScaleError
  apply mul_le_mul_of_nonneg_left _ hlR.le
  apply sub_le_sub_right
  apply exp_le_exp.mpr
  apply mul_le_mul hrhi _ (exp_pos _).le ((Nat.cast_nonneg (Fintype.card V)).trans hrhi)
  apply exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right hh (show 0 ≤ 8*(l : ℝ) by positivity)
  calc
    -h/(8*l) = -(h/(8*l)) := by ring
    _ ≤ -(c*D^(9/10 : ℝ)/(8*l)) := neg_le_neg he
    _ = -(c/(8*l))*D^(9/10 : ℝ) := by ring

end ErdosGallai.Splitting

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Routing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

theorem routing_union_growth_step_of_boundary
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤
      h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  let E := P.interedges B Bᶜ
  let Ebad := E.filter (fun e => s(e.1, e.2) ∈ F)
  let Vbad := B.biUnion (fun v => ({v} : Finset V) ×ˢ (W v))
  let Enew := (Finset.univ : Finset V) ×ˢ (Bnext \ B)
  have hcover : E ⊆ Ebad ∪ Vbad ∪ Enew := by
    intro e he
    rcases P.mem_interedges_iff.mp he with ⟨hv, hw, hadj⟩
    have hnw : e.2 ∉ B := Finset.mem_compl.mp hw
    by_cases hdel : s(e.1, e.2) ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hdel⟩))
    by_cases hforbid : e.2 ∈ W e.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨e.1, hv, Finset.mem_product.mpr ⟨by simp, hforbid⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr
        ⟨hextend e.1 hv e.2 hnw hadj hdel hforbid, hnw⟩⟩
  have hcount : E.card ≤ Ebad.card + Vbad.card + Enew.card :=
    (Finset.card_le_card hcover).trans <|
      (Finset.card_union_le _ _).trans <|
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hforbidden : Vbad.card ≤ ∑ v ∈ B, (W v).card := by
    simpa [Vbad, Finset.card_product] using
      (Finset.card_biUnion_le (s := B) (t := fun v => ({v} : Finset V) ×ˢ W v))
  have hnew : Enew.card = Fintype.card V * (Bnext \ B).card := by
    simp [Enew]
  have hraw : E.card ≤ Ebad.card + (∑ v ∈ B, (W v).card) +
      Fintype.card V * (Bnext \ B).card := by omega
  have hsum : (∑ v ∈ B, ((W v).card : ℝ)) ≤ (h / 4) * B.card := by
    calc
      _ ≤ ∑ _v ∈ B, h / 4 := Finset.sum_le_sum hW
      _ = _ := by simp [mul_comm]
  have hcomplN : B.card + Bᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ B)
  have hcompl : (B.card : ℝ) + (Bᶜ.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcomplN
  have hlecompl : (B.card : ℝ) ≤ (Bᶜ.card : ℝ) := by linarith
  have hcut : h * (B.card : ℝ) ≤ (E.card : ℝ) := by
    simpa [min_eq_left hlecompl, E] using hexp B
  have hdiffN : (Bnext \ B).card + B.card = Bnext.card := by
    rw [Finset.card_sdiff_of_subset hmono]
    exact Nat.sub_add_cancel (Finset.card_le_card hmono)
  have hdiff : ((Bnext \ B).card : ℝ) + (B.card : ℝ) = (Bnext.card : ℝ) := by
    exact_mod_cast hdiffN
  have hrawR : (E.card : ℝ) ≤ (Ebad.card : ℝ) +
      (∑ v ∈ B, ((W v).card : ℝ)) +
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    exact_mod_cast hraw
  have hreach : h * (B.card : ℝ) / 2 ≤
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    nlinarith [hcut, hrawR, hF, hsum]
  have hdiv : h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) ≤
      ((Bnext \ B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card V : ℝ))).mpr
    nlinarith [hreach]
  calc
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ)
        = (B.card : ℝ) + h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) := by ring
    _ ≤ (B.card : ℝ) + ((Bnext \ B).card : ℝ) := add_le_add (le_refl _) hdiv
    _ = (Bnext.card : ℝ) := by linarith

lemma root_mem_walkBall (G : SimpleGraph V) (s : V) (t : ℕ) :
    s ∈ walkBall G s t := by
  exact (mem_walkBall G s s t).mpr ⟨.nil, by simp⟩

lemma walkBall_mono (G : SimpleGraph V) (s : V) {t u : ℕ} (htu : t ≤ u) :
    walkBall G s t ⊆ walkBall G s u := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_walkBall G s v t).mp hv
  exact (mem_walkBall G s v u).mpr ⟨p, hp.trans htu⟩

lemma walk_avoids_end {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s v : V} (p : (avoidGraph P F W).Walk s v) (hs : s ∉ W) : v ∉ W := by
  induction p with
  | nil => exact hs
  | cons hadj p ih => exact ih hadj.2.2.2

lemma ball_avoids (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (t : ℕ) : Disjoint (walkBall (avoidGraph P F W) s t) W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨p, _⟩ := (mem_walkBall _ _ _ _).mp hv
  exact walk_avoids_end P F W p hs

lemma walkBall_step (G : SimpleGraph V) (s v w : V) (t : ℕ)
    (hv : v ∈ walkBall G s t) (hadj : G.Adj v w) :
    w ∈ walkBall G s (t + 1) := by
  obtain ⟨p, hp⟩ := (mem_walkBall _ _ _ _).mp hv
  apply (mem_walkBall _ _ _ _).mpr
  exact ⟨p.concat hadj, by simpa using Nat.add_le_add_right hp 1⟩

lemma CutExpansion.le_order (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) :
    h ≤ (Fintype.card V : ℝ) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcomplN : 1 ≤ ({v} : Finset V)ᶜ.card := by
    simp only [Finset.card_compl, Finset.card_singleton]
    omega
  have hcompl : (1 : ℝ) ≤ (({v} : Finset V)ᶜ.card : ℝ) := by exact_mod_cast hcomplN
  have hc := hexp {v}
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hcompl, mul_one] at hc
  have hupper := P.card_interedges_le_mul ({v} : Finset V) ({v} : Finset V)ᶜ
  simp only [Finset.card_singleton, one_mul] at hupper
  have hle := (Finset.card_le_univ (({v} : Finset V)ᶜ))
  exact hc.trans (by exact_mod_cast hupper.trans hle)

lemma routingG_growth (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    r / 2 < (1 + h / (2 * r)) ^ routingG r h := by
  have hr0 : 0 < r := by linarith
  let x := h / (2 * r)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    linarith
  have hlog : h / (4 * r) ≤ Real.log (1 + h / (2 * r)) := by
    have heq : h / (4 * r) = x / 2 := by dsimp [x]; ring
    rw [heq]
    calc
      x / 2 ≤ 2 * x / (x + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxle)]
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    exact htwo
  have hlogpos : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hbase : Real.log (2 * r) ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2pos).mpr
    nlinarith
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) :=
    Nat.le_ceil _
  have hlogpow : 2 * Real.log (2 * r) ≤
      Real.log ((1 + h / (2 * r)) ^ routingG r h) := by
    rw [Real.log_pow]
    calc
      2 * Real.log (2 * r) ≤ 2 * Real.logb 2 (2 * r) := by linarith
      _ = (8 * (r / h) * Real.logb 2 (2 * r)) * (h / (4 * r)) := by
        field_simp
        ; ring
      _ ≤ (routingG r h : ℝ) * (h / (4 * r)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (routingG r h : ℝ) * Real.log (1 + h / (2 * r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsmall : Real.log (r / 2) < 2 * Real.log (2 * r) := by
    have := Real.log_le_log (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 2 * r)
    linarith
  apply (Real.log_lt_log_iff (by positivity : 0 < r / 2) (by positivity)).mp
  exact hsmall.trans_le hlogpow

lemma incidentEdges_union {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (F E : Finset (Sym2 V)) (v : V) :
    incidentEdges (F ∪ E) v = incidentEdges F v ∪ incidentEdges E v := by
  simp [incidentEdges, Finset.filter_union]

lemma incidentEdges_union_card_le (F E : Finset (Sym2 V)) (v : V) :
    (incidentEdges (F ∪ E) v).card ≤ (incidentEdges F v).card + (incidentEdges E v).card := by
  rw [incidentEdges_union]
  exact Finset.card_union_le _ _

lemma incidentEdges_sum_le (F : Finset (Sym2 V)) :
    ∑ v : V, (incidentEdges F v).card ≤ 2 * F.card := by
  have heq : ∑ v : V, (incidentEdges F v).card = ∑ e ∈ F, e.toFinset.card := by
    simp only [incidentEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp [← Sym2.mem_toFinset]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e _ => by
      rw [Sym2.card_toFinset]
      split <;> norm_num)
    _ = 2 * F.card := by simp [mul_comm]

lemma incidentEdges_path_start_le_one {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset s).card ≤ 1 := by
  have hsub : incidentEdges p.edges.toFinset s ⊆ {s(s, p.snd)} := by
    intro e he
    obtain ⟨heP, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp hs
    subst e
    have hv := hp.eq_snd_of_mem_edges (List.mem_toFinset.mp heP)
    simp [hv]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma incidentEdges_path_end_le_one (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset t).card ≤ 1 := by
  simpa using incidentEdges_path_start_le_one G p.reverse hp.reverse

lemma incidentEdges_walk_eq_empty_of_not_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t v : V}
    (p : G.Walk s t) (hv : v ∉ p.support) : incidentEdges p.edges.toFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heP, hve⟩ := Finset.mem_filter.mp he
  have hm := p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, List.mem_toFinset.mp heP, hve⟩)
  exact hv hm

lemma incidentEdges_path_le_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) (v : V) :
    (incidentEdges p.edges.toFinset v).card ≤ 2 := by
  by_cases hv : v ∈ p.support
  · have htake := incidentEdges_path_end_le_one G (p.takeUntil v hv) (hp.takeUntil hv)
    have hdrop := incidentEdges_path_start_le_one G (p.dropUntil v hv) (hp.dropUntil hv)
    have heq : p.edges.toFinset = (p.takeUntil v hv).edges.toFinset ∪ (p.dropUntil v hv).edges.toFinset := by
      have he := congrArg (fun q : G.Walk s t => q.edges.toFinset) (p.take_spec hv)
      simpa only [SimpleGraph.Walk.edges_append, List.toFinset_append] using he.symm
    rw [heq]
    exact (incidentEdges_union_card_le _ _ v).trans (by omega)
  · rw [incidentEdges_walk_eq_empty_of_not_mem G p hv]
    simp

lemma deleted_boundary_card_le_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (B : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤
      ∑ v ∈ B, (incidentEdges F v).card := by
  let T := B.biUnion (fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  have hc : ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun e : V × V => (e.1, s(e.1, e.2)))
    · intro e he
      obtain ⟨heP, heF⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨e.1, (P.mem_interedges_iff.mp heP).1, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨heF, by simp⟩
    · intro e he f hf heq
      have hsym := congrArg Prod.snd heq
      exact boundary_sym2_injective P B (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hsym
  have hT : T.card ≤ ∑ v ∈ B, (incidentEdges F v).card := by
    simpa [T] using Finset.card_biUnion_le (s := B)
      (t := fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  exact hc.trans hT

lemma walkBall_growth_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) (t : ℕ)
    (hsmall : ((walkBall (avoidGraph P F W) s t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (walkBall (avoidGraph P F W) s t).card ≤
      ((walkBall (avoidGraph P F W) s (t + 1)).card : ℝ) := by
  classical
  apply routing_union_growth_step_of_boundary P h hexp hr F _ _ (fun _ => W)
      (walkBall_mono _ s (Nat.le_succ t)) hsmall
  · calc
      _ ≤ ∑ v ∈ walkBall (avoidGraph P F W) s t, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P (walkBall (avoidGraph P F W) s t) F
      _ ≤ ∑ _v ∈ walkBall (avoidGraph P F W) s t, h / 4 := Finset.sum_le_sum (fun v _ => hF v)
      _ = _ := by simp; ring
  · exact fun _ _ => hW
  · intro v hv w _ hadj hdel hw
    have hnv := Finset.disjoint_left.mp (ball_avoids P F W s hs t) hv
    exact walkBall_step _ s v w t hv ⟨hadj, hdel, hnv, hw⟩

lemma walkBall_large_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F W) s (routingG (Fintype.card V) h)).card := by
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < Fintype.card V := by linarith
  let g := routingG (Fintype.card V) h
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  by_contra hnot
  have hend := le_of_not_gt hnot
  have hpow : ∀ j ≤ g, c ^ j ≤ (walkBall (avoidGraph P F W) s j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have H := Finset.card_pos.mpr ⟨s, root_mem_walkBall (avoidGraph P F W) s 0⟩
      have H' : 1 ≤ (walkBall (avoidGraph P F W) s 0).card := H
      simpa using (Nat.cast_le (α := ℝ)).mpr H'
    | succ j ih =>
      intro hj
      have hmono : ((walkBall (avoidGraph P F W) s j).card : ℝ) ≤
          (walkBall (avoidGraph P F W) s g).card := by
        exact_mod_cast Finset.card_le_card (walkBall_mono (avoidGraph P F W) s (by omega : j ≤ g))
      have hsmall := hmono.trans hend
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * (walkBall (avoidGraph P F W) s j).card := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ (walkBall (avoidGraph P F W) s (j + 1)).card :=
          walkBall_growth_of_incidents P h hexp hr0 F W s hs hF hW j hsmall
  have hg := routingG_growth (Fintype.card V) h (by linarith) hh (hexp.le_order P h hr)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma exists_short_avoiding_path (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : (avoidGraph P F W).Walk s t, q.IsPath ∧
      q.length ≤ 2 * routingG (Fintype.card V) h := by
  classical
  let g := routingG (Fintype.card V) h
  let B₁ := walkBall (avoidGraph P F W) s g
  let B₂ := walkBall (avoidGraph P F W) t g
  have h₁ := walkBall_large_of_incidents P h hh hexp hr F W s hs hF hW
  have h₂ := walkBall_large_of_incidents P h hh hexp hr F W t ht hF hW
  have hmeet : (B₁ ∩ B₂).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_union_add_card_inter B₁ B₂
    have hu := Finset.card_le_univ (B₁ ∪ B₂)
    have hsum : (Fintype.card V : ℝ) < (B₁.card : ℝ) + (B₂.card : ℝ) := by
      dsimp [B₁, B₂, g]; linarith
    have hsumN : Fintype.card V < B₁.card + B₂.card := by exact_mod_cast hsum
    omega
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨p₁, hp₁⟩ := (mem_walkBall _ s v g).mp (Finset.mem_inter.mp hv).1
  obtain ⟨p₂, hp₂⟩ := (mem_walkBall _ t v g).mp (Finset.mem_inter.mp hv).2
  let w := p₁.append p₂.reverse
  refine ⟨w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans ?_⟩
  dsimp [w]
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

lemma two_routingG_le_length (r h : ℝ) : 2 * routingG r h ≤ routingLength r h := by
  dsimp [routingLength]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma routingLength_bounds (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) :
    1 ≤ routingLength r h ∧ r ≤ (routingLength r h : ℝ) * h := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * r)
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) := Nat.le_ceil _
  have hgh : 8 * r ≤ (routingG r h : ℝ) * h := by
    calc
      8 * r = (8 * (r / h)) * h := by field_simp
      _ ≤ (8 * (r / h) * Real.logb 2 (2 * r)) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (r / h) by positivity)
      _ ≤ (routingG r h : ℝ) * h := mul_le_mul_of_nonneg_right hg hh.le
  have hgpos : 0 < routingG r h := by
    have hgR : (0 : ℝ) < routingG r h := by nlinarith
    exact_mod_cast hgR
  have hgle : routingG r h ≤ routingLength r h := (by omega : routingG r h ≤ 2 * routingG r h).trans (two_routingG_le_length r h)
  refine ⟨by omega, ?_⟩
  have hgleR : (routingG r h : ℝ) ≤ routingLength r h := by exact_mod_cast hgle
  nlinarith

lemma routing_budget (L k b z h r : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hz : 0 ≤ z) (hh : 0 < h) (_hr : 0 ≤ r)
    (hreach : r ≤ L * h) (hbudget : 64 * (L ^ 2 * (k + b) + z) ≤ h) :
    h / 8 + 2 + k ≤ h / 4 ∧ z + b * L ≤ h / 8 ∧ 64 * L * k * r ≤ h ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLLs : L ≤ L ^ 2 := by nlinarith
  have hbig : 64 * (k + b) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : 0 ≤ k + b)]
      _ ≤ _ := hbudget
  have hbL : 64 * (b * L + z) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_left hLLs hb0, mul_nonneg (sq_nonneg L) hk0]
      _ ≤ _ := hbudget
  have hkL : 64 * L ^ 2 * k ≤ h := by nlinarith [mul_nonneg (sq_nonneg L) hb0]
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    64 * L * k * r ≤ 64 * L * k * (L * h) := mul_le_mul_of_nonneg_left hreach (by positivity)
    _ = (64 * L ^ 2 * k) * h := by ring
    _ ≤ h * h := mul_le_mul_of_nonneg_right hkL hh.le
    _ = h ^ 2 := by ring

lemma saturated_card_le (F : Finset (Sym2 V)) (h : ℝ) (hh : 0 < h)
    (hF : 128 * (F.card : ℝ) ≤ h ^ 2) : (saturated F h).card ≤ h / 8 := by
  classical
  have hs : h / 8 * (saturated F h).card ≤ ∑ v : V, ((incidentEdges F v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ saturated F h, h / 8 := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F h, ((incidentEdges F v).card : ℝ) := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsum : (∑ v : V, ((incidentEdges F v).card : ℝ)) ≤ 2 * (F.card : ℝ) := by
    exact_mod_cast incidentEdges_sum_le F
  nlinarith

lemma pathInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : SimpleGraph V} {s t : V} (q : P.Walk s t) :
    (pathInterior q).card ≤ q.length := by
  have hp := List.toFinset_card_le q.support
  rw [q.length_support] at hp
  have hstart : s ∈ q.support.toFinset ∩ ({s, t} : Finset V) := by simp
  have hint := Finset.card_pos.mpr ⟨s, hstart⟩
  have hd := Finset.card_sdiff_add_card_inter q.support.toFinset ({s, t} : Finset V)
  dsimp [pathInterior]
  omega

lemma avoidGraph_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    avoidGraph P F W ≤ P := fun _ _ h => h.1

lemma walk_avoids_support (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) (hs : s ∉ W) :
    Disjoint q.support.toFinset W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  exact walk_avoids_end P F W (q.takeUntil v (List.mem_toFinset.mp hv)) hs

lemma walk_avoids_edges {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) :
    Disjoint q.edges.toFinset F := by
  apply Finset.disjoint_left.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w => exact (q.adj_of_mem_edges (List.mem_toFinset.mp he)).2.1

lemma exists_short_path_with_avoidance (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ routingLength (Fintype.card V) h ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  obtain ⟨q, hp, hl⟩ := exists_short_avoiding_path P h hh hexp hr F W s t hs ht hF hW
  refine ⟨q.mapLe (avoidGraph_le P F W), hp.mapLe _, ?_, ?_, ?_⟩
  · simpa using hl.trans (two_routingG_le_length (Fintype.card V) h)
  · simpa using walk_avoids_edges P F W q
  · simpa using walk_avoids_support P F W q hs

lemma route_degree_update {P : SimpleGraph V} {s t : V} (q : P.Walk s t)
    (hp : q.IsPath) (F : Finset (Sym2 V)) (h : ℝ) (load : V → ℕ)
    (hdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 8 + 2 + load v)
    (havoid : Disjoint q.support.toFinset (saturated F h \ {s, t})) (v : V) :
    ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      h / 8 + 2 + load v + (if v = s ∨ v = t then 1 else 0) := by
  classical
  have hadd : ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      (incidentEdges F v).card + (incidentEdges q.edges.toFinset v).card := by
    exact_mod_cast incidentEdges_union_card_le F q.edges.toFinset v
  by_cases hv : v = s ∨ v = t
  · rw [ite_eq_left hv]
    have hqN : (incidentEdges q.edges.toFinset v).card ≤ 1 := by
      rcases hv with rfl | rfl
      · exact incidentEdges_path_start_le_one P q hp
      · exact incidentEdges_path_end_le_one P q hp
    have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 1 := by exact_mod_cast hqN
    linarith [hdegree v]
  · rw [ite_eq_right hv]
    by_cases hmem : v ∈ q.support
    · have hns : v ∉ saturated F h := by
        intro hsat
        apply Finset.disjoint_left.mp havoid (List.mem_toFinset.mpr hmem)
        exact Finset.mem_sdiff.mpr ⟨hsat, by simpa using hv⟩
      have hsmall : ((incidentEdges F v).card : ℝ) < h / 8 := by
        simpa [saturated] using hns
      have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 2 := by
        exact_mod_cast incidentEdges_path_le_two P q hp v
      have : (0 : ℝ) ≤ load v := by positivity
      linarith
    · rw [incidentEdges_walk_eq_empty_of_not_mem P q hmem] at hadd
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hadd
      linarith [hdegree v]

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

lemma endpointLoad_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {A B : Finset I} (hAB : A ⊆ B) (x y : I → V) (v : V) :
    endpointLoad A x y v ≤ endpointLoad B x y v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

lemma endpointLoad_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (i : I) (hi : i ∉ A) (x y : I → V) (v : V) :
    endpointLoad (insert i A) x y v = endpointLoad A x y v +
      (if v = x i ∨ v = y i then 1 else 0) := by
  classical
  by_cases hv : v = x i ∨ v = y i
  · have hv' : x i = v ∨ y i = v := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv', hi]
  · have hv' : ¬ (x i = v ∨ y i = v) := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv']

lemma endpointLoad_sum {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (x y : I → V) (hxy : ∀ i ∈ A, x i ≠ y i) :
    ∑ v : V, endpointLoad A x y v = 2 * A.card := by
  classical
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have heq : ∀ i ∈ A, (∑ v : V, if x i = v ∨ y i = v then 1 else 0) = 2 := by
    intro i hi
    have hf : (Finset.univ.filter fun v => x i = v ∨ y i = v) = ({x i, y i} : Finset V) := by
      ext v
      simp [eq_comm]
    have hc : ({x i, y i} : Finset V).card = 2 := by simp [hxy i hi]
    rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ _i ∈ A, 2 := Finset.sum_congr rfl heq
    _ = _ := by simp [mul_comm]

lemma usedEdges_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) (L : ℕ)
    (hq : ∀ i ∈ A, (q i).length ≤ L) : (usedEdges A q).card ≤ L * A.card := by
  calc
    _ ≤ ∑ i ∈ A, (q i).edges.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, L := Finset.sum_le_sum (fun i hi => by
      have hc := List.toFinset_card_le (q i).edges
      simpa using hc.trans (by simpa using hq i hi))
    _ = _ := by simp [mul_comm]

lemma usedEdges_update_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (i : I) (hi : i ∉ A)
    (q : ∀ j, P.Walk (x j) (y j)) (p : P.Walk (x i) (y i)) :
    usedEdges (insert i A) (Function.update q i p) = usedEdges A q ∪ p.edges.toFinset := by
  classical
  rw [usedEdges, Finset.biUnion_insert]
  simp only [Function.update_self]
  rw [Finset.union_comm]
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

lemma teamInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} {T : Type} [_contextInstance5 : Fintype I] [_contextInstance6 : DecidableEq I] [_contextInstance7 : DecidableEq T] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) (L : ℕ) (b : ℝ)
    (hq : ∀ j ∈ A, (q j).length ≤ L)
    (hb : ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b) :
    ((teamInterior A q team i).card : ℝ) ≤ b * L := by
  have hc : (teamInterior A q team i).card ≤ L * (A.filter (fun j => team j = team i)).card := by
    calc
      _ ≤ ∑ j ∈ A.filter (fun j => team j = team i), (pathInterior (q j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A.filter (fun j => team j = team i), L := Finset.sum_le_sum (fun j hj =>
        (pathInterior_card_le (q j)).trans (hq j (Finset.mem_filter.mp hj).1))
      _ = _ := by simp [mul_comm]
  have hcard : ((A.filter (fun j => team j = team i)).card : ℝ) ≤ b := by
    apply le_trans _ hb
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
  have hcR : ((teamInterior A q team i).card : ℝ) ≤ (L : ℝ) * (A.filter (fun j => team j = team i)).card := by exact_mod_cast hc
  calc
    _ ≤ (L : ℝ) * b := hcR.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = _ := mul_comm _ _

theorem routing (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ) ^ 2 * (k + b) + z) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let L := routingLength (Fintype.card V) h
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  obtain ⟨hL, hreach⟩ := routingLength_bounds (Fintype.card V) h (by linarith) hh
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hdegBudget, hforbidBudget, hnumBudget⟩ := routing_budget L k b z h (Fintype.card V)
    hLR hk hb hz hh (by positivity) hreach hbudget
  have hloadA : ∀ (A : Finset I) v, (endpointLoad A x y v : ℝ) ≤ k := by
    intro A v
    have hm : (endpointLoad A x y v : ℝ) ≤ endpointLoad Finset.univ x y v := by
      exact_mod_cast endpointLoad_mono (Finset.subset_univ A) x y v
    exact hm.trans (hload v)
  have htotal : 2 * (Fintype.card I : ℝ) ≤ k * Fintype.card V := by
    have heq := endpointLoad_sum Finset.univ x y (fun i _ => hxy i)
    have heqR : (∑ v : V, (endpointLoad Finset.univ x y v : ℝ)) = 2 * Fintype.card I := by
      exact_mod_cast heq
    rw [← heqR]
    calc
      _ ≤ ∑ _v : V, k := Finset.sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [mul_comm]
  have hdefault : ∀ i, ∃ p : P.Walk (x i) (y i), p.IsPath := by
    intro i
    obtain ⟨p, hp, _⟩ := exists_short_path_with_avoidance P h hh hexp hr ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨p, hp⟩
  choose defaultPath hdefaultPath using hdefault
  have hpartial : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i), PartialRoutes P x y team Z L h A q := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultPath, ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [usedEdges, Finset.biUnion_empty, incidentEdges, Finset.filter_empty,
          Finset.card_empty, Nat.cast_zero, endpointLoad, add_zero]
        linarith
    | @insert i A hi ih =>
      obtain ⟨q, hq⟩ := ih
      let F := usedEdges A q
      let S := saturated F h
      let B := teamInterior A q team i
      let W := (S ∪ Z i ∪ B) \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hc : (F.card : ℝ) ≤ (L : ℝ) * A.card := by
          exact_mod_cast usedEdges_card_le A q L hq.short
        have ha : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ A
        have hsize : 2 * (A.card : ℝ) ≤ k * Fintype.card V := by linarith
        have hmult := mul_le_mul_of_nonneg_left hsize (show 0 ≤ (L : ℝ) by positivity)
        nlinarith [hnumBudget]
      have hS : (S.card : ℝ) ≤ h / 8 := saturated_card_le F h hh hFcard
      have hB : (B.card : ℝ) ≤ b * L := teamInterior_card_le A q team i L b hq.short (hteam i)
      have hW : (W.card : ℝ) ≤ h / 4 := by
        have hc : W.card ≤ S.card + (Z i).card + B.card :=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        have hcR : (W.card : ℝ) ≤ (S.card : ℝ) + (Z i).card + B.card := by exact_mod_cast hc
        linarith [hZ i]
      have hFdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        intro v
        have hd := hq.degree v
        have hl := hloadA A v
        dsimp [F]
        linarith
      obtain ⟨p, hp, hpL, hpF, hpW⟩ := exists_short_path_with_avoidance P h hh hexp hr F W (x i) (y i)
        (by simp [W]) (by simp [W]) hFdegree hW
      have hpZ : Disjoint (pathInterior p) (Z i) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvZ
        obtain ⟨hvp, hvends⟩ := Finset.mem_sdiff.mp hv
        apply Finset.disjoint_left.mp hpW hvp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hvZ), hvends⟩
      have hpS : Disjoint p.support.toFinset (saturated F h \ {x i, y i}) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvS
        obtain ⟨hs, he⟩ := Finset.mem_sdiff.mp hvS
        apply Finset.disjoint_left.mp hpW hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hs), he⟩
      have hpEdge : ∀ j ∈ A, Disjoint p.edges.toFinset (q j).edges.toFinset := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro e hep heq
        exact Finset.disjoint_left.mp hpF hep (Finset.mem_biUnion.mpr ⟨j, hj, heq⟩)
      have hpTeam : ∀ j ∈ A, team i = team j → Disjoint (pathInterior p) (pathInterior (q j)) := by
        intro j hj htm
        apply Finset.disjoint_left.mpr
        intro v hvp hvq
        obtain ⟨hvp', hvends⟩ := Finset.mem_sdiff.mp hvp
        apply Finset.disjoint_left.mp hpW hvp'
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ ?_, hvends⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, htm.symm⟩, hvq⟩
      let q' := Function.update q i p
      have hsame : q' i = p := Function.update_self i p q
      have hother : ∀ j ∈ A, q' j = q j := by
        intro j hj
        apply Function.update_of_ne
        intro hji
        exact hi (hji ▸ hj)
      refine ⟨q', ?_⟩
      constructor
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hp
        · simpa only [hother j hj] using hq.simple j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpL
        · simpa only [hother j hj] using hq.short j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpZ
        · simpa only [hother j hj] using hq.avoids j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpEdge k hkA
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpEdge j hjA).symm
          · simpa only [hother j hjA, hother k hkA] using hq.edge_disjoint j hjA k hkA hjk
      · intro j hj k hk hjk htm
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpTeam k hkA htm
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpTeam j hjA htm.symm).symm
          · simpa only [hother j hjA, hother k hkA] using hq.team_disjoint j hjA k hkA hjk htm
      · intro v
        have heq : usedEdges (insert i A) q' = F ∪ p.edges.toFinset := usedEdges_update_insert A i hi q p
        rw [heq]
        have hu := route_degree_update p hp F h (endpointLoad A x y) hq.degree hpS v
        have hloadEq : (endpointLoad (insert i A) x y v : ℝ) =
            endpointLoad A x y v + (if v = x i ∨ v = y i then (1 : ℝ) else 0) := by
          rw [endpointLoad_insert A i hi]
          split_ifs <;> simp
        rw [hloadEq]
        simpa only [add_assoc] using hu
  obtain ⟨q, hq⟩ := hpartial Finset.univ
  exact ⟨q, fun i => ⟨hq.simple i (by simp), hq.short i (by simp), hq.avoids i (by simp)⟩,
    fun i j hij => hq.edge_disjoint i (by simp) j (by simp) hij,
    fun i j hij htm => hq.team_disjoint i (by simp) j (by simp) hij htm⟩

end Families
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Real Filter Asymptotics

lemma routing_length_upper (r h : ℝ) (hr : 2 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    (routingLength r h : ℝ) ≤ 108*(r/h)*(logb 2 r)^2 := by
  have hr0 : 0 < r := by linarith
  have hl : 1 ≤ logb 2 r := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 2) hr
  have hR : 1 ≤ r/h := (le_div_iff₀ hh).mpr (by simpa using hhr)
  have hlog : logb 2 (2*r) = 1 + logb 2 r := by
    rw [Real.logb_mul (by norm_num) hr0.ne']
    norm_num
  have hg := Nat.ceil_lt_add_one (show 0 ≤ 8*(r/h)*logb 2 (2*r) by rw [hlog]; positivity)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ logb 2 r by linarith)
  change (routingG r h : ℝ) < 8*(r/h)*logb 2 (2*r)+1 at hg
  change (routingDepth r : ℝ) < logb 2 r + 1 at hd
  rw [hlog] at hg
  have hprod : 1 ≤ (r/h)*logb 2 r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
  have hg' : (routingG r h : ℝ) ≤ 18*(r/h)*logb 2 r := by nlinarith
  have hd' : (1 + routingDepth r : ℝ) ≤ 3*logb 2 r := by linarith
  have hm := mul_le_mul hg' hd' (by positivity) (by positivity)
  dsimp [routingLength]
  push_cast
  nlinarith

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

theorem eventually_routing_length (c β γ δ : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 2 ≤ r → r ≤ D^β → c*D^γ ≤ r →
      (routingLength r (c*D^γ) : ℝ) ≤ D^(β-γ+δ) := by
  filter_upwards [eventually_logb_le_power (δ/4) (by positivity),
    eventually_constant_le_power (108*β^2/c) (δ/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with D hlog hconst hD r hr hrD hhr
  have hD0 : 0 < D := by linarith
  have hpowγ : 0 < D^γ := Real.rpow_pos_of_pos hD0 _
  have hden : 0 < c*D^γ := mul_pos hc hpowγ
  have hlog0 : 0 ≤ logb 2 r := (Real.logb_pos (by norm_num) (by linarith)).le
  have hlogR : logb 2 r ≤ β*D^(δ/4) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by linarith : 0 < r) hrD
    rw [Real.logb_rpow_eq_mul_logb_of_pos hD0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog hβ.le)
  have hratio : r/(c*D^γ) ≤ D^(β-γ)/c := by
    calc
      _ ≤ D^β/(c*D^γ) := div_le_div_of_nonneg_right hrD hden.le
      _ = _ := by rw [Real.rpow_sub hD0]; ring
  have hsq : (logb 2 r)^2 ≤ β^2*D^(δ/2) := by
    calc
      _ ≤ (β*D^(δ/4))^2 := pow_le_pow_left₀ hlog0 hlogR 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]; congr 2; ring
  calc
    (routingLength r (c*D^γ) : ℝ) ≤ 108*(r/(c*D^γ))*(logb 2 r)^2 :=
      routing_length_upper r (c*D^γ) hr hden hhr
    _ ≤ 108*(D^(β-γ)/c)*(β^2*D^(δ/2)) := by gcongr
    _ = (108*β^2/c)*D^(β-γ+δ/2) := by rw [Real.rpow_add hD0]; ring
    _ ≤ D^(δ/2)*D^(β-γ+δ/2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hD0.le _)
    _ = D^(β-γ+δ) := by rw [← Real.rpow_add hD0]; congr 1; ring

theorem batch_routing_margin : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
    2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
      (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
      2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
    filter_upwards [eventually_routing_length (1/4) (51/50) (9/10) (2/25)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_const_mul_power_le 1024 (7/10) (9/10) (by norm_num),
      eventually_constant_le_power 2 (9/10) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcost htwo hD r hr hrD
    have hD0 : 0 < D := by linarith
    have hr2 : 2 ≤ r := htwo.trans hr
    have hh : (1/4)*D^(9/10:ℝ) ≤ r := by
      have hh0 := Real.rpow_nonneg hD0.le (9/10:ℝ)
      linarith
    have hL := hlen r hr2 hrD hh
    norm_num at hL
    have hL' : (routingLength r (D^(9/10:ℝ)/4) : ℝ) ≤ D^(1/5:ℝ) := by
      convert hL using 1 ; ring_nf
    have hsmall : D^(1/100:ℝ) ≤ D^(3/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have h37 : D^(3/10:ℝ) ≤ D^(7/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have hprod : (routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ)) ≤ 2*D^(7/10:ℝ) := by
      calc
        _ ≤ (D^(1/5:ℝ))^2 * (2*D^(3/10:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    refine ⟨hr2, ?_⟩
    nlinarith only [hprod, h37, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

lemma subtype_image_compl {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W : Finset V) (U : Finset (W : Set V)) :
    Uᶜ.image Subtype.val = W \ U.image Subtype.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx (Subtype.ext he ▸ hy)
  · rintro ⟨hv,hvU⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro hx
    exact hvU ⟨⟨v,hv⟩,hx,rfl⟩

lemma induced_interedges_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (U : Finset (W : Set V)) :
    (((P.induce (W : Set V)).interedges U Uᶜ).card : ℝ) =
      ((P.interedges (U.image Subtype.val) (W \ U.image Subtype.val)).card : ℝ) := by
  classical
  let f : ↥(W : Set V) × ↥(W : Set V) → V × V := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have heq : ((P.induce (W : Set V)).interedges U Uᶜ).image f =
      P.interedges (U.image Subtype.val) (W \ U.image Subtype.val) := by
    rw [← subtype_image_compl W U]
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩
      exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
    · rintro ⟨⟨x,hx,hxe⟩,⟨y,hy,hye⟩,he⟩
      refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext hxe hye⟩
      change P.Adj x.val y.val
      simpa only [hxe,hye] using he
  rw [← heq, Finset.card_image_of_injective _ hf]

lemma cutExpansion_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (hexp : CutExpansionOn P W h) :
    CutExpansion (P.induce (W : Set V)) h := by
  classical
  intro U
  have hsub : U.image Subtype.val ⊆ W := by
    rintro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have h := hexp (U.image Subtype.val) hsub
  have he : W \ U.image Subtype.val = Uᶜ.image Subtype.val :=
    (subtype_image_compl W U).symm
  rw [he] at h
  simp only [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [induced_interedges_card,he]
  exact h

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.PathDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

lemma PositiveSimplePath.endpoints_ne {V : Type cycleUniverse2} {G : SimpleGraph V}
    (P : PositiveSimplePath G) : P.start ≠ P.finish := by
  intro he
  have hz := P.isPath.nil_iff_eq.mpr he
  have := hz.length_eq_zero
  have := P.positive
  omega

theorem endpoint_path_count {V : Type cycleUniverse3} {I : Type cycleUniverse4} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hload : ∀ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hsum : (∑ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card) =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heq : ∀ i : I,
        (∑ v : V, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : (Finset.univ.filter fun v =>
          (P i).start = v ∨ (P i).finish = v) = {(P i).start, (P i).finish} := by
        ext v; simp [eq_comm]
      have hc : ({(P i).start, (P i).finish} : Finset V).card = 2 := by
        simp [(P i).endpoints_ne]
      rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hload v)
  rw [hsum] at hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem evenAugmentation_degree {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).degree (some v) =
      G.degree v + if Even (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp only [evenAugmentation_some_adj, evenAugmentation_some_none]
  have he : (∑ u : V, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  omega

theorem evenAugmentation_old_odd {V : Type cycleUniverse13} [Fintype V]
    (G : SimpleGraph V) (v : V) : Odd ((evenAugmentation G).degree (some v)) := by
  rw [evenAugmentation_degree]
  by_cases h : Even (G.degree v)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · simpa [h] using Nat.not_even_iff_odd.mp h

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem trail_partition_degree_sum {V : Type cycleUniverse14} {I : Type cycleUniverse15} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse16} {I : Type cycleUniverse17} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

private theorem odd_load_one {V : Type cycleUniverse18} [DecidableEq V]
    (S : Finset V) (f : V → ℕ) (ho : ∀ v ∈ S, Odd (f v))
    (hs : ∑ v ∈ S, f v ≤ S.card + 1) : ∀ v ∈ S, f v = 1 := by
  intro v hv
  by_contra hn
  have hv3 : 3 ≤ f v := by rcases ho v hv with ⟨k, hk⟩; omega
  have hlow : ∑ x ∈ S, (1 + if x = v then 2 else 0) ≤ ∑ x ∈ S, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = v
    · subst x; simpa using hv3
    · simp only [he, ↓reduceIte, add_zero]
      rcases ho x hx with ⟨k, hk⟩
      omega
  have heq : (∑ x ∈ S, (1 + if x = v then 2 else 0)) = S.card + 2 := by
    simp [Finset.sum_add_distrib, hv]
  omega

theorem tight_odd_trail_partition {V : Type cycleUniverse19} {I : Type cycleUniverse20} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) {a b : I → V}
    (p : ∀ i, G.Walk (a i) (b i)) (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v))
    (hsize : 2 * Fintype.card I ≤ S.card + 1) :
    (∀ i, a i ≠ b i) ∧ (∀ v ∈ S,
      (Finset.univ.filter (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card = 1) := by
  classical
  let load := fun v : V => (Finset.univ.filter
    (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card
  let openParts := Finset.univ.filter (fun i => a i ≠ b i)
  have hlodd : ∀ v ∈ S, Odd (load v) := by
    intro v hv
    rw [← Nat.not_even_iff_odd, ← trail_partition_even_degree_iff G p ht hd hc v]
    exact (Nat.not_even_iff_odd.mpr (ho v hv))
  have htotal : (∑ v : V, load v) = 2 * openParts.card := by
    dsimp [load]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he : ∀ i : I, (∑ v : V, if a i ≠ b i ∧ (v = a i ∨ v = b i) then 1 else 0) =
        if a i ≠ b i then 2 else 0 := by
      intro i
      by_cases h : a i = b i
      · simp [h]
      · have hf : (Finset.univ.filter (fun v => a i ≠ b i ∧ (v = a i ∨ v = b i))) =
            {a i, b i} := by ext v; simp [h]
        have hcard : ({a i, b i} : Finset V).card = 2 := by simp [h]
        rw [ite_eq_left h, ← hcard, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change openParts.card * 2 = 2 * openParts.card
    omega
  have hsub : (∑ v ∈ S, load v) ≤ ∑ v : V, load v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hlow : S.card ≤ ∑ v ∈ S, load v := by
    simpa using Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := load)
      (fun v hv => by rcases hlodd v hv with ⟨k, hk⟩; omega)
  have hcount : openParts.card ≤ Fintype.card I := Finset.card_le_univ _
  have hpoint := odd_load_one S load hlodd (by omega)
  refine ⟨?_, hpoint⟩
  intro i hi
  have hproper : openParts ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hh : i ∈ openParts := heq.symm ▸ Finset.mem_univ i
    simp [openParts, hi] at hh
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem delete_vertex_boundary_edges {V : Type cycleUniverse25} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) :
    (0 < (p.takeUntil v hv).dropLast.length →
      s((p.takeUntil v hv).penultimate, v) ∈ p.edgeSet) ∧
    (0 < (p.dropUntil v hv).tail.length →
      s(v, (p.dropUntil v hv).snd) ∈ p.edgeSet) := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  constructor
  · intro hpos
    have hn : ¬ t.Nil := by
      intro hz
      change 0 < t.dropLast.length at hpos
      rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hpos
      omega
    have hm := t.mk_penultimate_end_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inl hm
  · intro hpos
    have hn : ¬ d.Nil := by
      intro hz
      change 0 < d.tail.length at hpos
      rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hpos
      omega
    have hm := d.mk_start_snd_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inr hm

theorem delete_vertex_new_ends_ne {V : Type cycleUniverse26} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support)
    (hl : 0 < (p.takeUntil v hv).dropLast.length)
    (hr : 0 < (p.dropUntil v hv).tail.length) :
    (p.takeUntil v hv).penultimate ≠ (p.dropUntil v hv).snd := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  have htn : ¬t.Nil := by
    intro hz
    change 0 < t.dropLast.length at hl
    rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hl
    omega
  have hdn : ¬d.Nil := by
    intro hz
    change 0 < d.tail.length at hr
    rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hr
    omega
  have hdj := hp.isTrail.edges_nodup
  rw [← heq, SimpleGraph.Walk.edges_append] at hdj
  have hdis := (List.nodup_append.mp hdj).2.2
  intro hsame
  have ha := t.mk_penultimate_end_mem_edges htn
  have hb := d.mk_start_snd_mem_edges hdn
  apply hdis _ ha _ hb

  rw [show t.penultimate = d.snd from hsame, Sym2.eq_swap]

theorem delete_vertex_new_endpoint_load {V : Type cycleUniverse27} {I : Type cycleUniverse28} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {a b : I → V} {v : V}
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsPath)
    (hv : ∀ i, v ∈ (p i).support)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (x : V) :
    let live := fun z : I × Bool => if z.2 then
      0 < ((p z.1).takeUntil v (hv z.1)).dropLast.length else
      0 < ((p z.1).dropUntil v (hv z.1)).tail.length
    let newEnd := fun z : I × Bool => if z.2 then
      ((p z.1).takeUntil v (hv z.1)).penultimate else
      ((p z.1).dropUntil v (hv z.1)).snd
    (Finset.univ.filter fun z => live z ∧ newEnd z = x).card ≤ 1 := by
  classical
  dsimp only
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨i, bi⟩ := z
  obtain ⟨j, bj⟩ := w
  have hi := (Finset.mem_filter.mp hz).2
  have hj := (Finset.mem_filter.mp hw).2
  have hei : s(v,x) ∈ (p i).edgeSet := by
    cases bi
    · have hx : ((p i).dropUntil v (hv i)).snd = x := hi.2
      simpa only [hx] using (delete_vertex_boundary_edges (p i) (hv i)).2 hi.1
    · have hx : ((p i).takeUntil v (hv i)).penultimate = x := hi.2
      have he := (delete_vertex_boundary_edges (p i) (hv i)).1 hi.1
      simpa only [hx, Sym2.eq_swap] using he
  have hej : s(v,x) ∈ (p j).edgeSet := by
    cases bj
    · have hx : ((p j).dropUntil v (hv j)).snd = x := hj.2
      simpa only [hx] using (delete_vertex_boundary_edges (p j) (hv j)).2 hj.1
    · have hx : ((p j).takeUntil v (hv j)).penultimate = x := hj.2
      have he := (delete_vertex_boundary_edges (p j) (hv j)).1 hj.1
      simpa only [hx, Sym2.eq_swap] using he
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) hei hej
  subst j
  congr 1
  cases bi <;> cases bj
  · rfl
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hj.1 hi.1
    exact (he (hj.2.trans hi.2.symm)).elim
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hi.1 hj.1
    exact (he (hi.2.trans hj.2.symm)).elim
  · rfl

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deleted_ends {V : Type cycleUniverse32} {I : Type cycleUniverse33} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v x : V) (j : DeleteIndex p v) :
    (deleted p v j).start = x ∨ (deleted p v j).finish = x ↔
      oldEnd p v x j ∨ newEnd p v x j := by
  rcases j with i | ⟨i,b⟩
  · simp [deleted, oldEnd, newEnd]
  · cases b <;> simp [deleted, oldEnd, newEnd, or_comm]

lemma deleted_edges_subset {V : Type cycleUniverse34} {I : Type cycleUniverse35} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v) :
    (deleted p v j).walk.edgeSet ⊆ (p (parent p v j)).walk.edgeSet := by
  rcases j with i | ⟨i,b⟩
  · exact Set.Subset.rfl
  · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
    cases b
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inr he).1
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inl he).1

lemma deleted_disjoint (p : I → SimplePathPiece G) (v : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    Pairwise fun j k => Disjoint (deleted p v j).walk.edgeSet (deleted p v k).walk.edgeSet := by
  intro j k hjk
  by_cases he : parent p v j = parent p v k
  · rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
    · exact (hjk (congrArg Sum.inl (Subtype.ext he))).elim
    · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
    · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
    · have hil : i = l := Subtype.ext he
      subst l
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1
      · exact (hjk rfl).elim
  · exact (hd he).mono (deleted_edges_subset p v j) (deleted_edges_subset p v k)

lemma deleted_old_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => oldEnd p v x j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjp : (p (parent p v j)).start = x ∨ (p (parent p v j)).finish = x := by
    have h := (Finset.mem_filter.mp hj).2
    rcases j with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have hkp : (p (parent p v k)).start = x ∨ (p (parent p v k)).finish = x := by
    have h := (Finset.mem_filter.mp hk).2
    rcases k with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have he := Finset.card_le_one.mp hload (parent p v j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjp⟩) (parent p v k)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
  · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
  · have hil : i = l := Subtype.ext he
    subst l
    cases b <;> cases c
    · rfl
    · exact (hne _ (hk'.trans hj'.symm)).elim
    · exact (hne _ (hj'.trans hk'.symm)).elim
    · rfl

lemma deleted_new_load (p : I → SimplePathPiece G) (v x : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧ newEnd p v x j).card ≤ 1 := by
  classical
  have h := delete_vertex_new_endpoint_load
    (fun i : Meeting p v => (p i.val).walk) (fun i => (p i.val).isPath)
    (fun i => i.property)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) x
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩
  · exact False.elim hj'.2
  rcases k with l | ⟨l,c⟩
  · exact False.elim hk'.2
  apply congrArg Sum.inr
  apply Finset.card_le_one.mp h
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases b <;> exact hj'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases c <;> exact hk'

theorem deleted_endpoint_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun j : DeleteIndex p v => oldEnd p v x j)
  let B := Finset.univ.filter (fun j : DeleteIndex p v =>
    0 < (deleted p v j).walk.length ∧ newEnd p v x j)
  have hsub : (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)) ⊆ A ∪ B := by
    intro j hj
    obtain ⟨hpos,hend⟩ := (Finset.mem_filter.mp hj).2
    rcases (deleted_ends p v x j).mp hend with ho | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hn⟩)
  have ha := deleted_old_load p v x hne hload
  have hb := deleted_new_load p v x hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A,B] at hc
  omega

theorem deleted_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : DeleteIndex p v, (deleted p v j).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨⟨parent p v j, deleted_edges_subset p v j hj⟩,?_⟩
    rcases j with i | ⟨i,b⟩
    · intro hv
      exact i.property (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e,hj,hv⟩))
    · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
      cases b
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inr hj).2
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inl hj).2
  · rintro ⟨⟨i,hi⟩,hv⟩
    by_cases hs : v ∈ (p i).walk.support
    · have h := (delete_vertex_from_path (p i).walk (p i).isPath hs).2.2.2.1
      have he : e ∈ ((p i).walk.takeUntil v hs).dropLast.edgeSet ∪
          ((p i).walk.dropUntil v hs).tail.edgeSet := h.symm ▸ ⟨hi,hv⟩
      rcases he with hl | hr
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩

theorem deleted_positive_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length},
      (deleted p v j.val).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  rw [← deleted_union p v]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hp : 0 < (deleted p v j).walk.length := by
      by_contra hn
      have hz : (deleted p v j).walk.length = 0 := by omega
      have hn' := SimpleGraph.Walk.length_eq_zero_iff.mp hz
      have he' := SimpleGraph.Walk.edges_eq_nil.mpr hn'
      have hmem : e ∈ (deleted p v j).walk.edges := hj
      exact List.not_mem_nil (he' ▸ hmem)
    exact Set.mem_iUnion.mpr ⟨⟨j,hp⟩,hj⟩

end SimplePathPiece

end
end ErdosGallai
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.EndpointPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

theorem endpoint_partition_after_deletion (p : I → SimplePathPiece G) (v : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hc : (⋃ i, (p i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, x ≠ v → (Finset.univ.filter fun i =>
      (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    EndpointPathPartition (G.induce {x | x ≠ v}) := by
  classical
  let A := {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}
  let f : G.induce {x | x ≠ v} →g G := (SimpleGraph.Embedding.induce _).toHom
  have hf : Function.Injective f := Subtype.val_injective
  apply endpoint_partition_of_family (fun j : A => deletedPositive p v j)
  · intro j k hjk
    have hdis := deleted_disjoint p v hd (fun he => hjk (Subtype.ext he))
    apply Set.disjoint_left.mpr
    intro e hej hek
    have he1 : Sym2.map f e ∈ (deleted p v j.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v j]
      exact ⟨e,hej,rfl⟩
    have he2 : Sym2.map f e ∈ (deleted p v k.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v k]
      exact ⟨e,hek,rfl⟩
    exact Set.disjoint_left.mp hdis he1 he2
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact (deletedPositive p v j).walk.edges_subset_edgeSet hj
    · intro e he
      have he' : Sym2.map f e ∈ G.edgeSet ∧ v ∉ Sym2.map f e := by
        induction e using Sym2.inductionOn with | _ a b =>
          refine ⟨he,?_⟩
          change v ∉ s(a.val,b.val)
          simpa only [Sym2.map_mk,Sym2.mem_iff,eq_comm] using not_or.mpr ⟨a.property,b.property⟩
      have hmem : Sym2.map f e ∈ ⋃ j : A, (deleted p v j.val).walk.edgeSet := by
        rw [deleted_positive_union]
        refine ⟨?_,he'.2⟩
        exact Set.mem_iUnion.mp (hc.symm ▸ he'.1)
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hmem
      rw [← deletedInduced_edges p v j] at hj
      obtain ⟨e',he',heq⟩ := hj
      have heq' : e' = e := Sym2.map.injective hf heq
      subst e'
      exact Set.mem_iUnion.mpr ⟨j,he'⟩
  · intro x
    have hb := deleted_endpoint_load p v x.val hne hd (hl x.val x.property)
    have hc' : (Finset.univ.filter fun j : A =>
        (deletedPositive p v j).start = x ∨ (deletedPositive p v j).finish = x).card ≤
        (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
          ((deleted p v j).start = x.val ∨ (deleted p v j).finish = x.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,j.property,?_⟩
        rcases (Finset.mem_filter.mp hj).2 with hs | ht
        · exact Or.inl (congrArg Subtype.val hs)
        · exact Or.inr (congrArg Subtype.val ht)
      · exact fun _ _ _ _ he => Subtype.ext he
    refine le_trans (le_of_eq (congrArg Finset.card ?_)) (hc'.trans hb)
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end SimplePathPiece

theorem endpoint_partition_of_augmented_parts {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (hL : LovaszPathCyclePartition (evenAugmentation G)) :
    EndpointPathPartition G := by
  classical
  obtain ⟨k,parts,hparts,hd,hc,hk⟩ := hL
  have hw : ∀ i : Fin k, ∃ (a b : Option V) (p : (evenAugmentation G).Walk a b),
      p.IsTrail ∧ (a ≠ b → p.IsPath) ∧ parts i = p.edgeSet := by
    intro i
    rcases hparts i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
    · exact ⟨a,b,p,hp.isTrail,fun _ => hp,he⟩
    · exact ⟨a,a,p,hp.isTrail,fun h => False.elim (h rfl),he⟩
  choose a b p ht hp he using hw
  have hd' : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet := by
    simpa only [he] using hd
  have hc' : (⋃ i, (p i).edgeSet) = (evenAugmentation G).edgeSet := by
    simpa only [he] using hc
  let S : Finset (Option V) := Finset.univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,Finset.card_image_of_injective _ (Option.some_injective V),Finset.card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact evenAugmentation_old_odd G y
  have hk' : 2 * Fintype.card (Fin k) ≤ S.card + 1 := by
    simpa only [Fintype.card_fin,Fintype.card_option,hS] using hk
  obtain ⟨hopen,hload⟩ := tight_odd_trail_partition (evenAugmentation G) S p ht hd' hc' ho hk'
  let P : Fin k → SimplePathPiece (evenAugmentation G) := fun i =>
    ⟨a i,b i,p i,hp i (hopen i)⟩
  have hload' : ∀ x : Option V, x ≠ none → (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 1 := by
    intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x =>
      have h := hload (some x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      have hpred : (Finset.univ.filter fun i => a i ≠ b i ∧
          (some x = a i ∨ some x = b i)) =
          (Finset.univ.filter fun i => (P i).start = some x ∨ (P i).finish = some x) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,P]
        constructor
        · rintro ⟨_,hi⟩
          exact hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · intro hi
          exact ⟨hopen i,hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
      apply le_of_eq
      calc
        _ = _ := congrArg Finset.card hpred.symm
        _ = 1 := by
          convert h using 1
          congr 1
          ext i
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]

  have hdel := SimplePathPiece.endpoint_partition_after_deletion P none hopen hd' hc' hload'
  exact endpoint_partition_mapIso (evenAugmentationOldIso G).symm hdel

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G :=
  lovasz_path_cycle_decomposition G

theorem endpoint_path_partition {V : Type cycleUniverse14} [Fintype V] (G : SimpleGraph V) :
    EndpointPathPartition G :=
  endpoint_partition_of_augmented_parts G (lovasz_path_cycle_partition (evenAugmentation G))

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

noncomputable section
open SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

theorem edgeDecomposition_assemble {V I : Type} [Fintype I] (G : SimpleGraph V)
    (W : I → Type) (H : ∀ i, SimpleGraph (W i))
    (f : ∀ i, H i →g G) (hf : ∀ i, Function.Injective (f i))
    (hdisj : Pairwise (fun i j =>
      Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
    (hcover : (⋃ i, Sym2.map (f i) '' (H i).edgeSet) = G.edgeSet)
    (k : I → ℕ) (hparts : ∀ i, EdgeDecomposition (H i) (k i)) :
    EdgeDecomposition G (∑ i, k i) := by
  classical
  choose parts hp hd hu using hparts
  let J := Σ i, Fin (k i)
  let P : J → Set (Sym2 V) := fun j => Sym2.map (f j.1) '' parts j.1 j.2
  have hpart : ∀ j, CycleOrSingleEdge G (P j) := by
    intro j; exact cycleOrSingleEdge_map (f j.1) (hf j.1) (hp j.1 j.2)
  have hsub : ∀ i a, parts i a ⊆ (H i).edgeSet := by
    intro i a; exact cycleOrSingleEdge_subset (hp i a)
  have hdisjP : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases h : i = j
    · subst j
      have hab : a ≠ b := fun he => hij (by cases he; rfl)
      apply Set.disjoint_left.mpr
      rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
      have hxy : x = y := Sym2.map.injective (hf i) (he.trans he'.symm)
      subst y
      exact Set.disjoint_left.mp (hd i hab) hx hy
    · exact (hdisj h).mono (Set.image_mono (hsub i a)) (Set.image_mono (hsub j b))
  have hcoverP : (⋃ j, P j) = G.edgeSet := by
    rw [← hcover]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,a⟩,x,hx,he⟩
      exact ⟨i,x,hsub i a hx,he⟩
    · rintro ⟨i,x,hx,he⟩
      rw [← hu i] at hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i,a⟩,x,ha,he⟩
  have hc : Fintype.card J = ∑ i, k i := by simp [J, Fintype.card_sigma]
  rw [← hc]
  exact edgeDecomposition_of_indexed G P hpart hdisjP hcoverP

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma edgeDecomposition_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f)
    (hu : Sym2.map f '' H.edgeSet = G.edgeSet) {k : ℕ} (hk : EdgeDecomposition H k) :
    EdgeDecomposition G k := by
  have := edgeDecomposition_assemble (I := Unit) G (fun _ : Unit => W) (fun _ => H) (fun _ => f)
    (fun _ => hf) (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
    (by rw [Set.iUnion_const]; exact hu) (fun _ => k) (fun _ => hk)
  simpa using this

lemma edgeDecomposition_on {V : Type} (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A)
    {k : ℕ} (hk : EdgeDecomposition (G.induce (A:Set V)) k) : EdgeDecomposition G k := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  apply edgeDecomposition_map f Subtype.val_injective _ hk
  ext e
  constructor
  · rintro ⟨e,he,rfl⟩
    induction e using Sym2.ind with | _ x y => exact he
  · intro he
    induction e using Sym2.ind with
    | _ x y => exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchPathDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable

lemma PositiveSimplePath.endpoints_ne {V : Type cycleUniverse2} {G : SimpleGraph V}
    (P : PositiveSimplePath G) : P.start ≠ P.finish := by
  intro he
  have hz := P.isPath.nil_iff_eq.mpr he
  have := hz.length_eq_zero
  have := P.positive
  omega

theorem endpoint_path_count {V : Type cycleUniverse3} {I : Type cycleUniverse4} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hload : ∀ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hsum : (∑ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card) =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heq : ∀ i : I,
        (∑ v : V, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : (Finset.univ.filter fun v =>
          (P i).start = v ∨ (P i).finish = v) = {(P i).start, (P i).finish} := by
        ext v; simp [eq_comm]
      have hc : ({(P i).start, (P i).finish} : Finset V).card = 2 := by
        simp [(P i).endpoints_ne]
      rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hload v)
  rw [hsum] at hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  omega

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem evenAugmentation_degree {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).degree (some v) =
      G.degree v + if Even (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp only [evenAugmentation_some_adj, evenAugmentation_some_none]
  have he : (∑ u : V, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  omega

theorem evenAugmentation_old_odd {V : Type cycleUniverse13} [Fintype V]
    (G : SimpleGraph V) (v : V) : Odd ((evenAugmentation G).degree (some v)) := by
  rw [evenAugmentation_degree]
  by_cases h : Even (G.degree v)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · simpa [h] using Nat.not_even_iff_odd.mp h

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem trail_partition_degree_sum {V : Type cycleUniverse14} {I : Type cycleUniverse15} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse16} {I : Type cycleUniverse17} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

private theorem odd_load_one {V : Type cycleUniverse18} [DecidableEq V]
    (S : Finset V) (f : V → ℕ) (ho : ∀ v ∈ S, Odd (f v))
    (hs : ∑ v ∈ S, f v ≤ S.card + 1) : ∀ v ∈ S, f v = 1 := by
  intro v hv
  by_contra hn
  have hv3 : 3 ≤ f v := by rcases ho v hv with ⟨k, hk⟩; omega
  have hlow : ∑ x ∈ S, (1 + if x = v then 2 else 0) ≤ ∑ x ∈ S, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = v
    · subst x; simpa using hv3
    · simp only [he, ↓reduceIte, add_zero]
      rcases ho x hx with ⟨k, hk⟩
      omega
  have heq : (∑ x ∈ S, (1 + if x = v then 2 else 0)) = S.card + 2 := by
    simp [Finset.sum_add_distrib, hv]
  omega

theorem tight_odd_trail_partition {V : Type cycleUniverse19} {I : Type cycleUniverse20} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) {a b : I → V}
    (p : ∀ i, G.Walk (a i) (b i)) (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v))
    (hsize : 2 * Fintype.card I ≤ S.card + 1) :
    (∀ i, a i ≠ b i) ∧ (∀ v ∈ S,
      (Finset.univ.filter (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card = 1) := by
  classical
  let load := fun v : V => (Finset.univ.filter
    (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card
  let openParts := Finset.univ.filter (fun i => a i ≠ b i)
  have hlodd : ∀ v ∈ S, Odd (load v) := by
    intro v hv
    rw [← Nat.not_even_iff_odd, ← trail_partition_even_degree_iff G p ht hd hc v]
    exact (Nat.not_even_iff_odd.mpr (ho v hv))
  have htotal : (∑ v : V, load v) = 2 * openParts.card := by
    dsimp [load]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he : ∀ i : I, (∑ v : V, if a i ≠ b i ∧ (v = a i ∨ v = b i) then 1 else 0) =
        if a i ≠ b i then 2 else 0 := by
      intro i
      by_cases h : a i = b i
      · simp [h]
      · have hf : (Finset.univ.filter (fun v => a i ≠ b i ∧ (v = a i ∨ v = b i))) =
            {a i, b i} := by ext v; simp [h]
        have hcard : ({a i, b i} : Finset V).card = 2 := by simp [h]
        rw [ite_eq_left h, ← hcard, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change openParts.card * 2 = 2 * openParts.card
    omega
  have hsub : (∑ v ∈ S, load v) ≤ ∑ v : V, load v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hlow : S.card ≤ ∑ v ∈ S, load v := by
    simpa using Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := load)
      (fun v hv => by rcases hlodd v hv with ⟨k, hk⟩; omega)
  have hcount : openParts.card ≤ Fintype.card I := Finset.card_le_univ _
  have hpoint := odd_load_one S load hlodd (by omega)
  refine ⟨?_, hpoint⟩
  intro i hi
  have hproper : openParts ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hh : i ∈ openParts := heq.symm ▸ Finset.mem_univ i
    simp [openParts, hi] at hh
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section

theorem delete_vertex_boundary_edges {V : Type cycleUniverse25} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) :
    (0 < (p.takeUntil v hv).dropLast.length →
      s((p.takeUntil v hv).penultimate, v) ∈ p.edgeSet) ∧
    (0 < (p.dropUntil v hv).tail.length →
      s(v, (p.dropUntil v hv).snd) ∈ p.edgeSet) := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  constructor
  · intro hpos
    have hn : ¬ t.Nil := by
      intro hz
      change 0 < t.dropLast.length at hpos
      rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hpos
      omega
    have hm := t.mk_penultimate_end_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inl hm
  · intro hpos
    have hn : ¬ d.Nil := by
      intro hz
      change 0 < d.tail.length at hpos
      rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hpos
      omega
    have hm := d.mk_start_snd_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inr hm

theorem delete_vertex_new_ends_ne {V : Type cycleUniverse26} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support)
    (hl : 0 < (p.takeUntil v hv).dropLast.length)
    (hr : 0 < (p.dropUntil v hv).tail.length) :
    (p.takeUntil v hv).penultimate ≠ (p.dropUntil v hv).snd := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  have htn : ¬t.Nil := by
    intro hz
    change 0 < t.dropLast.length at hl
    rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hl
    omega
  have hdn : ¬d.Nil := by
    intro hz
    change 0 < d.tail.length at hr
    rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hr
    omega
  have hdj := hp.isTrail.edges_nodup
  rw [← heq, SimpleGraph.Walk.edges_append] at hdj
  have hdis := (List.nodup_append.mp hdj).2.2
  intro hsame
  have ha := t.mk_penultimate_end_mem_edges htn
  have hb := d.mk_start_snd_mem_edges hdn
  apply hdis _ ha _ hb

  rw [show t.penultimate = d.snd from hsame, Sym2.eq_swap]

theorem delete_vertex_new_endpoint_load {V : Type cycleUniverse27} {I : Type cycleUniverse28} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {a b : I → V} {v : V}
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsPath)
    (hv : ∀ i, v ∈ (p i).support)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (x : V) :
    let live := fun z : I × Bool => if z.2 then
      0 < ((p z.1).takeUntil v (hv z.1)).dropLast.length else
      0 < ((p z.1).dropUntil v (hv z.1)).tail.length
    let newEnd := fun z : I × Bool => if z.2 then
      ((p z.1).takeUntil v (hv z.1)).penultimate else
      ((p z.1).dropUntil v (hv z.1)).snd
    (Finset.univ.filter fun z => live z ∧ newEnd z = x).card ≤ 1 := by
  classical
  dsimp only
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨i, bi⟩ := z
  obtain ⟨j, bj⟩ := w
  have hi := (Finset.mem_filter.mp hz).2
  have hj := (Finset.mem_filter.mp hw).2
  have hei : s(v,x) ∈ (p i).edgeSet := by
    cases bi
    · have hx : ((p i).dropUntil v (hv i)).snd = x := hi.2
      simpa only [hx] using (delete_vertex_boundary_edges (p i) (hv i)).2 hi.1
    · have hx : ((p i).takeUntil v (hv i)).penultimate = x := hi.2
      have he := (delete_vertex_boundary_edges (p i) (hv i)).1 hi.1
      simpa only [hx, Sym2.eq_swap] using he
  have hej : s(v,x) ∈ (p j).edgeSet := by
    cases bj
    · have hx : ((p j).dropUntil v (hv j)).snd = x := hj.2
      simpa only [hx] using (delete_vertex_boundary_edges (p j) (hv j)).2 hj.1
    · have hx : ((p j).takeUntil v (hv j)).penultimate = x := hj.2
      have he := (delete_vertex_boundary_edges (p j) (hv j)).1 hj.1
      simpa only [hx, Sym2.eq_swap] using he
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) hei hej
  subst j
  congr 1
  cases bi <;> cases bj
  · rfl
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hj.1 hi.1
    exact (he (hj.2.trans hi.2.symm)).elim
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hi.1 hj.1
    exact (he (hi.2.trans hj.2.symm)).elim
  · rfl

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deleted_ends {V : Type cycleUniverse32} {I : Type cycleUniverse33} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v x : V) (j : DeleteIndex p v) :
    (deleted p v j).start = x ∨ (deleted p v j).finish = x ↔
      oldEnd p v x j ∨ newEnd p v x j := by
  rcases j with i | ⟨i,b⟩
  · simp [deleted, oldEnd, newEnd]
  · cases b <;> simp [deleted, oldEnd, newEnd, or_comm]

lemma deleted_edges_subset {V : Type cycleUniverse34} {I : Type cycleUniverse35} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v) :
    (deleted p v j).walk.edgeSet ⊆ (p (parent p v j)).walk.edgeSet := by
  rcases j with i | ⟨i,b⟩
  · exact Set.Subset.rfl
  · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
    cases b
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inr he).1
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inl he).1

lemma deleted_disjoint (p : I → SimplePathPiece G) (v : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    Pairwise fun j k => Disjoint (deleted p v j).walk.edgeSet (deleted p v k).walk.edgeSet := by
  intro j k hjk
  by_cases he : parent p v j = parent p v k
  · rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
    · exact (hjk (congrArg Sum.inl (Subtype.ext he))).elim
    · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
    · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
    · have hil : i = l := Subtype.ext he
      subst l
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1
      · exact (hjk rfl).elim
  · exact (hd he).mono (deleted_edges_subset p v j) (deleted_edges_subset p v k)

lemma deleted_old_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => oldEnd p v x j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjp : (p (parent p v j)).start = x ∨ (p (parent p v j)).finish = x := by
    have h := (Finset.mem_filter.mp hj).2
    rcases j with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have hkp : (p (parent p v k)).start = x ∨ (p (parent p v k)).finish = x := by
    have h := (Finset.mem_filter.mp hk).2
    rcases k with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have he := Finset.card_le_one.mp hload (parent p v j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjp⟩) (parent p v k)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
  · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
  · have hil : i = l := Subtype.ext he
    subst l
    cases b <;> cases c
    · rfl
    · exact (hne _ (hk'.trans hj'.symm)).elim
    · exact (hne _ (hj'.trans hk'.symm)).elim
    · rfl

lemma deleted_new_load (p : I → SimplePathPiece G) (v x : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧ newEnd p v x j).card ≤ 1 := by
  classical
  have h := delete_vertex_new_endpoint_load
    (fun i : Meeting p v => (p i.val).walk) (fun i => (p i.val).isPath)
    (fun i => i.property)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) x
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩
  · exact False.elim hj'.2
  rcases k with l | ⟨l,c⟩
  · exact False.elim hk'.2
  apply congrArg Sum.inr
  apply Finset.card_le_one.mp h
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases b <;> exact hj'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases c <;> exact hk'

theorem deleted_endpoint_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun j : DeleteIndex p v => oldEnd p v x j)
  let B := Finset.univ.filter (fun j : DeleteIndex p v =>
    0 < (deleted p v j).walk.length ∧ newEnd p v x j)
  have hsub : (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)) ⊆ A ∪ B := by
    intro j hj
    obtain ⟨hpos,hend⟩ := (Finset.mem_filter.mp hj).2
    rcases (deleted_ends p v x j).mp hend with ho | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hn⟩)
  have ha := deleted_old_load p v x hne hload
  have hb := deleted_new_load p v x hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A,B] at hc
  omega

theorem deleted_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : DeleteIndex p v, (deleted p v j).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨⟨parent p v j, deleted_edges_subset p v j hj⟩,?_⟩
    rcases j with i | ⟨i,b⟩
    · intro hv
      exact i.property (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e,hj,hv⟩))
    · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
      cases b
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inr hj).2
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inl hj).2
  · rintro ⟨⟨i,hi⟩,hv⟩
    by_cases hs : v ∈ (p i).walk.support
    · have h := (delete_vertex_from_path (p i).walk (p i).isPath hs).2.2.2.1
      have he : e ∈ ((p i).walk.takeUntil v hs).dropLast.edgeSet ∪
          ((p i).walk.dropUntil v hs).tail.edgeSet := h.symm ▸ ⟨hi,hv⟩
      rcases he with hl | hr
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩

theorem deleted_positive_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length},
      (deleted p v j.val).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  rw [← deleted_union p v]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hp : 0 < (deleted p v j).walk.length := by
      by_contra hn
      have hz : (deleted p v j).walk.length = 0 := by omega
      have hn' := SimpleGraph.Walk.length_eq_zero_iff.mp hz
      have he' := SimpleGraph.Walk.edges_eq_nil.mpr hn'
      have hmem : e ∈ (deleted p v j).walk.edges := hj
      exact List.not_mem_nil (he' ▸ hmem)
    exact Set.mem_iUnion.mpr ⟨⟨j,hp⟩,hj⟩

end SimplePathPiece

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

theorem endpoint_partition_after_deletion (p : I → SimplePathPiece G) (v : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hc : (⋃ i, (p i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, x ≠ v → (Finset.univ.filter fun i =>
      (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    EndpointPathPartition (G.induce {x | x ≠ v}) := by
  classical
  let A := {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}
  let f : G.induce {x | x ≠ v} →g G := (SimpleGraph.Embedding.induce _).toHom
  have hf : Function.Injective f := Subtype.val_injective
  apply endpoint_partition_of_family (fun j : A => deletedPositive p v j)
  · intro j k hjk
    have hdis := deleted_disjoint p v hd (fun he => hjk (Subtype.ext he))
    apply Set.disjoint_left.mpr
    intro e hej hek
    have he1 : Sym2.map f e ∈ (deleted p v j.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v j]
      exact ⟨e,hej,rfl⟩
    have he2 : Sym2.map f e ∈ (deleted p v k.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v k]
      exact ⟨e,hek,rfl⟩
    exact Set.disjoint_left.mp hdis he1 he2
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact (deletedPositive p v j).walk.edges_subset_edgeSet hj
    · intro e he
      have he' : Sym2.map f e ∈ G.edgeSet ∧ v ∉ Sym2.map f e := by
        induction e using Sym2.inductionOn with | _ a b =>
          refine ⟨he,?_⟩
          change v ∉ s(a.val,b.val)
          simpa only [Sym2.map_mk,Sym2.mem_iff,eq_comm] using not_or.mpr ⟨a.property,b.property⟩
      have hmem : Sym2.map f e ∈ ⋃ j : A, (deleted p v j.val).walk.edgeSet := by
        rw [deleted_positive_union]
        refine ⟨?_,he'.2⟩
        exact Set.mem_iUnion.mp (hc.symm ▸ he'.1)
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hmem
      rw [← deletedInduced_edges p v j] at hj
      obtain ⟨e',he',heq⟩ := hj
      have heq' : e' = e := Sym2.map.injective hf heq
      subst e'
      exact Set.mem_iUnion.mpr ⟨j,he'⟩
  · intro x
    have hb := deleted_endpoint_load p v x.val hne hd (hl x.val x.property)
    have hc' : (Finset.univ.filter fun j : A =>
        (deletedPositive p v j).start = x ∨ (deletedPositive p v j).finish = x).card ≤
        (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
          ((deleted p v j).start = x.val ∨ (deleted p v j).finish = x.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,j.property,?_⟩
        rcases (Finset.mem_filter.mp hj).2 with hs | ht
        · exact Or.inl (congrArg Subtype.val hs)
        · exact Or.inr (congrArg Subtype.val ht)
      · exact fun _ _ _ _ he => Subtype.ext he
    refine le_trans (le_of_eq (congrArg Finset.card ?_)) (hc'.trans hb)
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end SimplePathPiece

theorem endpoint_partition_of_augmented_parts {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (hL : LovaszPathCyclePartition (evenAugmentation G)) :
    EndpointPathPartition G := by
  classical
  obtain ⟨k,parts,hparts,hd,hc,hk⟩ := hL
  have hw : ∀ i : Fin k, ∃ (a b : Option V) (p : (evenAugmentation G).Walk a b),
      p.IsTrail ∧ (a ≠ b → p.IsPath) ∧ parts i = p.edgeSet := by
    intro i
    rcases hparts i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
    · exact ⟨a,b,p,hp.isTrail,fun _ => hp,he⟩
    · exact ⟨a,a,p,hp.isTrail,fun h => False.elim (h rfl),he⟩
  choose a b p ht hp he using hw
  have hd' : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet := by
    simpa only [he] using hd
  have hc' : (⋃ i, (p i).edgeSet) = (evenAugmentation G).edgeSet := by
    simpa only [he] using hc
  let S : Finset (Option V) := Finset.univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,Finset.card_image_of_injective _ (Option.some_injective V),Finset.card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact evenAugmentation_old_odd G y
  have hk' : 2 * Fintype.card (Fin k) ≤ S.card + 1 := by
    simpa only [Fintype.card_fin,Fintype.card_option,hS] using hk
  obtain ⟨hopen,hload⟩ := tight_odd_trail_partition (evenAugmentation G) S p ht hd' hc' ho hk'
  let P : Fin k → SimplePathPiece (evenAugmentation G) := fun i =>
    ⟨a i,b i,p i,hp i (hopen i)⟩
  have hload' : ∀ x : Option V, x ≠ none → (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 1 := by
    intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x =>
      have h := hload (some x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      have hpred : (Finset.univ.filter fun i => a i ≠ b i ∧
          (some x = a i ∨ some x = b i)) =
          (Finset.univ.filter fun i => (P i).start = some x ∨ (P i).finish = some x) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,P]
        constructor
        · rintro ⟨_,hi⟩
          exact hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · intro hi
          exact ⟨hopen i,hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
      apply le_of_eq
      calc
        _ = _ := congrArg Finset.card hpred.symm
        _ = 1 := by
          convert h using 1
          congr 1
          ext i
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]

  have hdel := SimplePathPiece.endpoint_partition_after_deletion P none hopen hd' hc' hload'
  exact endpoint_partition_mapIso (evenAugmentationOldIso G).symm hdel

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G :=
  ErdosGallai.lovasz_path_cycle_decomposition G

theorem endpoint_path_partition {V : Type cycleUniverse14} [Fintype V] (G : SimpleGraph V) :
    EndpointPathPartition G :=
  endpoint_partition_of_augmented_parts G (lovasz_path_cycle_partition (evenAugmentation G))

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section

namespace Pairing
variable {V : Type cycleUniverse2} {W : Type cycleUniverse3}

theorem nonempty_of_even [Fintype V] (h : Even (Fintype.card V)) : Nonempty (Pairing V) := by
  classical
  obtain ⟨k,hk⟩ := h
  let q : Pairing (Fin k ⊕ Fin k) := ⟨fun x => x.swap,
    (by intro x; cases x <;> rfl), (by intro x h; cases x <;> nomatch h)⟩
  let e : (Fin k ⊕ Fin k) ≃ V := Fintype.equivOfCardEq (by simpa using hk.symm)
  exact ⟨transport e q⟩

variable [Fintype V]

theorem oneCount_transport (e : V ≃ V) (a b : V) :
    oneCount (e a) (e b) = oneCount a b := by
  classical
  symm
  exact Fintype.card_congr ((transport e).subtypeEquiv (by intro p; simp))

theorem oneCount_eq (a b c : V) (hab : a ≠ b) (hac : a ≠ c) :
    oneCount a b = oneCount a c := by
  classical
  have h := oneCount_transport (Equiv.swap b c) a b
  simpa [Equiv.swap_apply_of_ne_of_ne hab hac] using h.symm

theorem oneCount_balance (a b : V) (hab : a ≠ b) :
    (Fintype.card V - 1) * oneCount a b = Fintype.card (Pairing V) := by
  classical
  have hsum : (∑ c : V, oneCount a c) = Fintype.card (Pairing V) := by
    unfold oneCount
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun p : Pairing V => p a))
  have heq : (∑ c : V, oneCount a c) = ∑ c ∈ (univ.erase a), oneCount a b := by
    rw [← Finset.sum_erase_add _ _ (mem_univ a),oneCount_self,add_zero]
    apply Finset.sum_congr rfl
    intro c hc
    exact oneCount_eq a c b (Finset.mem_erase.mp hc).1.symm hab
  rw [heq,Finset.sum_const,Finset.card_erase_of_mem (mem_univ a)] at hsum
  simpa using hsum

theorem twoCount_transport (e : V ≃ V) (a b c d : V) :
    twoCount (e a) (e b) (e c) (e d) = twoCount a b c d := by
  classical
  symm
  exact Fintype.card_congr ((transport e).subtypeEquiv (by intro p; simp))

theorem twoCount_eq (a b c d e : V)
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) : twoCount a b c d = twoCount a b c e := by
  classical
  have h := twoCount_transport (Equiv.swap d e) a b c d
  simpa [Equiv.swap_apply_of_ne_of_ne had hae,
    Equiv.swap_apply_of_ne_of_ne hbd hbe,Equiv.swap_apply_of_ne_of_ne hcd hce] using h.symm

theorem twoCount_forbidden (a b c d : V) (hac : a ≠ c) (hbc : b ≠ c)
    (hd : d = a ∨ d = b ∨ d = c) : twoCount a b c d = 0 := by
  classical
  unfold twoCount
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun p => ?_⟩
  rcases p.property with ⟨hab,hcd⟩
  rcases hd with rfl | rfl | rfl
  · have h := congrArg p.val hcd
    simp only [apply_apply,hab] at h
    exact hbc h.symm
  · have h := congrArg p.val hab
    have h' := congrArg p.val hcd
    simp only [apply_apply] at h h'
    exact hac (h.trans h'.symm)
  · exact p.val.apply_ne _ hcd

theorem twoCount_balance (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Fintype.card V - 3) * twoCount a b c d = oneCount a b := by
  classical
  let Q := {p : Pairing V // p a = b}
  have hsum : (∑ e : V, twoCount a b c e) = oneCount a b := by
    have hcard : ∀ e : V, Fintype.card {p : Q // p.val c = e} = twoCount a b c e := by
      intro e
      apply Fintype.card_congr
      exact ⟨fun p => ⟨p.val.val,p.val.property,p.property⟩,
        fun p => ⟨⟨p.val,p.property.1⟩,p.property.2⟩,fun _ => rfl,fun _ => rfl⟩
    calc
      (∑ e : V, twoCount a b c e) = ∑ e : V, Fintype.card {p : Q // p.val c = e} := by simp_rw [hcard]
      _ = Fintype.card Q := by
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun p : Q => p.val c))
      _ = oneCount a b := rfl
  let S : Finset V := {a,b,c}
  have hScard : S.card = 3 := by simp [S,hab,hac,hbc]
  have hsum' : (∑ e : V, twoCount a b c e) = ∑ e ∈ univ \ S, twoCount a b c d := by
    rw [← Finset.sum_sdiff (s₁:=S) (s₂:=univ) (by simp)]
    have hz : ∑ e ∈ S, twoCount a b c e = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact twoCount_forbidden a b c e hac hbc (by simpa [S] using he)
    rw [hz,add_zero]
    apply Finset.sum_congr rfl
    intro e he
    have he' : e ≠ a ∧ e ≠ b ∧ e ≠ c := by simpa [S] using (Finset.mem_sdiff.mp he).2
    exact twoCount_eq a b c e d he'.1.symm had he'.2.1.symm hbd he'.2.2.symm hcd
  rw [hsum',Finset.sum_const,Finset.card_sdiff,Finset.inter_univ,hScard] at hsum
  simpa using hsum

theorem one_fraction (hV : Even (Fintype.card V)) (a b : V) (hab : a ≠ b) :
    (oneCount a b : ℝ) / Fintype.card (Pairing V) = 1 / (Fintype.card V - 1 : ℝ) := by
  classical
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.mpr ⟨a,b,hab⟩
  have hbal := oneCount_balance a b hab
  have hbal' : ((Fintype.card V:ℝ)-1)*(oneCount a b:ℝ) = Fintype.card (Pairing V) := by
    have h := congrArg (fun n : ℕ => (n:ℝ)) hbal
    simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using h
  have : Nonempty (Pairing V) := nonempty_of_even hV
  have hp : (0:ℝ) < Fintype.card (Pairing V) := by exact_mod_cast Fintype.card_pos
  have hn' : (0:ℝ) < Fintype.card V-1 := by
    have hnR : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  apply (div_eq_div_iff hp.ne' hn'.ne').mpr
  nlinarith

theorem two_fraction (hV : Even (Fintype.card V)) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (twoCount a b c d : ℝ) / Fintype.card (Pairing V) =
      1 / ((Fintype.card V - 1 : ℝ)*(Fintype.card V - 3 : ℝ)) := by
  classical
  have hn : 4 ≤ Fintype.card V := by
    have : ({a,b,c,d}:Finset V).card = 4 := by simp [hab,hac,had,hbc,hbd,hcd]
    exact this.symm ▸ Finset.card_le_univ _
  have hone := oneCount_balance a b hab
  have htwo := twoCount_balance a b c d hab hac had hbc hbd hcd
  have hb : ((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)*(twoCount a b c d:ℝ) =
      Fintype.card (Pairing V) := by
    have h1 : ((Fintype.card V:ℝ)-1)*(oneCount a b:ℝ) = Fintype.card (Pairing V) := by
      have h := congrArg (fun n : ℕ => (n:ℝ)) hone
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using h
    have h2 : ((Fintype.card V:ℝ)-3)*(twoCount a b c d:ℝ) = oneCount a b := by
      have h := congrArg (fun n : ℕ => (n:ℝ)) htwo
      simpa only [Nat.cast_mul,Nat.cast_sub (show 3 ≤ Fintype.card V by omega),Nat.cast_ofNat] using h
    nlinarith
  have : Nonempty (Pairing V) := nonempty_of_even hV
  have hp : (0:ℝ) < Fintype.card (Pairing V) := by exact_mod_cast Fintype.card_pos
  have hn' : (0:ℝ) < Fintype.card V-3 := by
    have hnR : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hn'' : (0:ℝ) < Fintype.card V-1 := by linarith
  apply (div_eq_div_iff hp.ne' (mul_pos hn'' hn').ne').mpr
  nlinarith

end Pairing
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section

lemma finiteAverage_equiv {α : Type cycleUniverse5} {β : Type cycleUniverse6} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : finiteAverage (fun x => f (e x)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp,Fintype.card_congr e]

lemma finiteAverage_add {α : Type cycleUniverse7} [Fintype α] (f g : α → ℝ) :
    finiteAverage (fun x => f x+g x) = finiteAverage f+finiteAverage g := by
  simp [finiteAverage,Finset.sum_add_distrib,add_div]

lemma finiteAverage_sum {α : Type cycleUniverse8} {ι : Type cycleUniverse9} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    finiteAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm,Finset.sum_div]

lemma finiteAverage_const {α : Type cycleUniverse11} [Fintype α] [Nonempty α] (r : ℝ) :
    finiteAverage (fun _ : α => r) = r := by
  have h : (Fintype.card α:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage,h]

lemma finiteAverage_mono {α : Type cycleUniverse12} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteAverage f ≤ finiteAverage g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun a _ => h a)

lemma finiteAverage_prod {α : Type cycleUniverse13} {β : Type cycleUniverse14} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    finiteAverage (fun x : α × β => f x.1*g x.2) = finiteAverage f*finiteAverage g := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

lemma exists_le_finiteAverage {α : Type cycleUniverse15} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ a, f a ≤ finiteAverage f := by
  have hp : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h : ∑ a, f a ≤ ∑ _a : α, finiteAverage f := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,finiteAverage]
    field_simp
    rfl
  obtain ⟨a,ha,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty) h
  exact ⟨a,h⟩

lemma finiteAverage_indicator {α : Type cycleUniverse16} [Fintype α] (P : α → Prop) [DecidablePred P] :
    finiteAverage (fun a => if P a then 1 else 0) = (Fintype.card {a // P a} : ℝ)/Fintype.card α := by
  unfold finiteAverage
  congr 1
  simp [Fintype.card_subtype]

lemma finiteAverage_pi_eval {ι : Type cycleUniverse17} [Fintype ι] [DecidableEq ι] {Ω : ι → Type cycleUniverse60}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (i : ι) (f : Ω i → ℝ) :
    finiteAverage (fun ω : ∀ j, Ω j => f (ω i)) = finiteAverage f := by
  classical
  let e := Equiv.piSplitAt i Ω
  have he := finiteAverage_equiv e.symm (fun ω : ∀ j, Ω j => f (ω i))
  have he' : finiteAverage (fun x : Ω i × (∀ j : {j // j ≠ i}, Ω j.val) => f x.1) =
      finiteAverage f := by
    have h := finiteAverage_prod f (fun _ : (∀ j : {j // j ≠ i}, Ω j.val) => (1:ℝ))
    simpa only [mul_one,finiteAverage_const] using h
  rw [← he]
  simpa [e,Equiv.piSplitAt_symm_apply] using he'

lemma finiteAverage_pi_pair {ι : Type cycleUniverse18} [Fintype ι] [DecidableEq ι] {Ω : ι → Type cycleUniverse61}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (i j : ι) (hij : i ≠ j)
    (f : Ω i → ℝ) (g : Ω j → ℝ) :
    finiteAverage (fun ω : ∀ k, Ω k => f (ω i)*g (ω j)) = finiteAverage f*finiteAverage g := by
  classical
  let e := Equiv.piSplitAt i Ω
  rw [← finiteAverage_equiv e.symm (fun ω : ∀ k, Ω k => f (ω i)*g (ω j))]
  have hfun : (fun x => f (e.symm x i)*g (e.symm x j)) =
      (fun x : Ω i × (∀ k : {k // k ≠ i}, Ω k.val) => f x.1*g (x.2 ⟨j,hij.symm⟩)) := by
    funext x
    simp [e,Equiv.piSplitAt_symm_apply,hij.symm]
  rw [hfun,finiteAverage_prod f (fun x : (∀ k : {k // k ≠ i}, Ω k.val) => g (x ⟨j,hij.symm⟩)),
    finiteAverage_pi_eval]

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section

lemma pairingSpace_even (V : Type cycleUniverse20) [Fintype V] :
    Even (Fintype.card (V ⊕ Fin (Fintype.card V % 2))) := by
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.even_iff]
  omega

instance pairingSpace_nonempty (V : Type cycleUniverse21) [Fintype V] : Nonempty (PairingSpace V) :=
  Pairing.nonempty_of_even (pairingSpace_even V)

lemma paired_symm {V : Type cycleUniverse25} [Fintype V] (p : PairingSpace V) {u v : V}
    (h : paired p u v) : paired p v u := by
  have hh := congrArg p h
  simpa only [paired,Pairing.apply_apply] using hh.symm

lemma paired_first_moment {V : Type cycleUniverse30} [Fintype V] (u v : V) (huv : u ≠ v) :
    finiteAverage (fun p : PairingSpace V => if paired p u v then 1 else 0) =
      1 / ((Fintype.card V:ℝ) + (Fintype.card V % 2 : ℕ) - 1) := by
  classical
  rw [finiteAverage_indicator]
  have h := Pairing.one_fraction (pairingSpace_even V) (Sum.inl u) (Sum.inl v)
    (by simpa using huv)
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at h
  dsimp only [Pairing.oneCount,paired] at h ⊢
  convert h using 1
  congr 2

lemma paired_two_moment {V : Type cycleUniverse31} [Fintype V] (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V => if paired p a b ∧ paired p c d then 1 else 0) =
      1 / (((Fintype.card V:ℝ)+(Fintype.card V%2:ℕ)-1)*
        ((Fintype.card V:ℝ)+(Fintype.card V%2:ℕ)-3)) := by
  classical
  rw [finiteAverage_indicator]
  have h := Pairing.two_fraction (pairingSpace_even V)
    (Sum.inl a) (Sum.inl b) (Sum.inl c) (Sum.inl d)
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at h
  dsimp only [Pairing.twoCount,paired] at h ⊢
  convert h using 1
  congr 2

lemma paired_first_bound {V : Type cycleUniverse32} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (u v : V) (huv : u ≠ v) :
    finiteAverage (fun p : PairingSpace V => if paired p u v then 1 else 0) ≤
      1 / ((Fintype.card V:ℝ)-1) := by
  classical
  rw [paired_first_moment u v huv]
  have hn : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hm : (0:ℝ) ≤ (Fintype.card V%2:ℕ) := Nat.cast_nonneg _
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma paired_two_bound {V : Type cycleUniverse33} [Fintype V] (hV : 4 ≤ Fintype.card V)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V => if paired p a b ∧ paired p c d then 1 else 0) ≤
      1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := by
  classical
  rw [paired_two_moment a b c d hab hac had hbc hbd hcd]
  have hn : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hm : (0:ℝ) ≤ (Fintype.card V%2:ℕ) := Nat.cast_nonneg _
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma finiteAverage_or_le {Ω : Type cycleUniverse34} [Fintype Ω] (P Q : Ω → Prop) :
    finiteAverage (fun ω => if P ω ∨ Q ω then 1 else 0) ≤
      finiteAverage (fun ω => if P ω then 1 else 0) +
      finiteAverage (fun ω => if Q ω then 1 else 0) := by
  rw [← finiteAverage_add]
  apply finiteAverage_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]

lemma pairing_patterns_internal {V : Type cycleUniverse36} [Fintype V] (hV : 4 ≤ Fintype.card V)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V =>
      if (paired p a c ∧ paired p b d) ∨ (paired p a d ∧ paired p b c) then 1 else 0) ≤
      2 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := by
  have h₁ := paired_two_bound hV a c b d hac hab had hbc.symm hcd hbd
  have h₂ := paired_two_bound hV a d b c had hab hac hbd.symm hcd.symm hbc
  have h := finiteAverage_or_le
    (fun p : PairingSpace V => paired p a c ∧ paired p b d)
    (fun p : PairingSpace V => paired p a d ∧ paired p b c)
  calc
    _ ≤ finiteAverage (fun p : PairingSpace V => if paired p a c ∧ paired p b d then 1 else 0) +
        finiteAverage (fun p : PairingSpace V => if paired p a d ∧ paired p b c then 1 else 0) := by
      convert h using 1 <;> congr 3 <;> funext p <;> split_ifs <;> rfl
    _ ≤ 1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) +
      1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := add_le_add h₁ h₂
    _ = _ := by ring

lemma pairing_patterns_cross {I : Type cycleUniverse37} [Fintype I] [DecidableEq I]
    {V : I → Type cycleUniverse63} [∀ i, Fintype (V i)] (i j : I) (hij : i ≠ j)
    (a c : V i) (hac : a ≠ c) (b d : V j) (hbd : b ≠ d) :
    finiteAverage (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then 1 else 0) =
      (1 / ((Fintype.card (V i):ℝ)+(Fintype.card (V i)%2:ℕ)-1)) *
      (1 / ((Fintype.card (V j):ℝ)+(Fintype.card (V j)%2:ℕ)-1)) := by
  have hind : (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then (1:ℝ) else 0) =
      (fun p => (if paired (p i) a c then 1 else 0)*(if paired (p j) b d then 1 else 0)) := by
    funext p
    split_ifs <;> simp_all
  rw [hind,finiteAverage_pi_pair (Ω:=fun k => PairingSpace (V k)) i j hij
    (fun p => if paired p a c then 1 else 0) (fun p => if paired p b d then 1 else 0),paired_first_moment a c hac,paired_first_moment b d hbd]

lemma pairing_patterns_cross_bound {I : Type cycleUniverse38} [Fintype I] [DecidableEq I]
    {V : I → Type cycleUniverse64} [∀ i, Fintype (V i)] (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ Fintype.card (V i)) (hj : 2 ≤ Fintype.card (V j))
    (a c : V i) (hac : a ≠ c) (b d : V j) (hbd : b ≠ d) :
    finiteAverage (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then 1 else 0) ≤
      1 / (((Fintype.card (V i):ℝ)-1)*((Fintype.card (V j):ℝ)-1)) := by
  rw [pairing_patterns_cross i j hij a c hac b d hbd,one_div_mul_one_div]
  have hi' : (2:ℝ) ≤ Fintype.card (V i) := by exact_mod_cast hi
  have hj' : (2:ℝ) ≤ Fintype.card (V j) := by exact_mod_cast hj
  have hmi : (0:ℝ) ≤ (Fintype.card (V i)%2:ℕ) := Nat.cast_nonneg _
  have hmj : (0:ℝ) ≤ (Fintype.card (V j)%2:ℕ) := Nat.cast_nonneg _
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
namespace Pairing
variable {V : Type cycleUniverse39}

lemma project_eq_iff (p : Pairing V) (u v : V) :
    project p u = project p v ↔ u = v ∨ p u = v := Quotient.eq

lemma project_surjective (p : Pairing V) : Function.Surjective (project p) := by
  intro q
  exact Quotient.exists_rep q

@[simp] lemma project_apply (p : Pairing V) (v : V) : project p (p v) = project p v :=
  (project_eq_iff p _ _).mpr (Or.inr (apply_apply p v))

lemma fiber_card [Fintype V] (p : Pairing V) (q : PairQuotient p) :
    Fintype.card {v // project p v = q} = 2 := by
  classical
  obtain ⟨x,rfl⟩ := project_surjective p q
  rw [Fintype.card_subtype]
  have heq : (univ.filter (fun v => project p v = project p x)) = {x,p x} := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [project_eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have hh := congrArg p h
        simpa only [apply_apply] using hh
    · rintro (h | h)
      · exact Or.inl h
      · right
        subst v
        simp
  rw [heq]
  simp [Ne.symm (apply_ne p x)]

lemma card_pairQuotient [Fintype V] (p : Pairing V) :
    2 * Fintype.card (PairQuotient p) = Fintype.card V := by
  classical
  have h : (∑ q : PairQuotient p, Fintype.card {v // project p v = q}) = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (project p))
  simpa only [fiber_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_comm] using h
end Pairing

lemma oldProject_eq_iff {V : Type cycleUniverse41} [Fintype V] (p : PairingSpace V) (u v : V) :
    oldProject p u = oldProject p v ↔ u = v ∨ paired p u v := by
  simp only [oldProject,Pairing.project_eq_iff,Sum.inl.injEq,paired]

lemma dummy_partner_is_old {V : Type cycleUniverse42} [Fintype V] (p : PairingSpace V)
    (d : Fin (Fintype.card V % 2)) : ∃ v : V, p (Sum.inr d) = Sum.inl v := by
  cases h : p (Sum.inr d) with
  | inl v => exact ⟨v,rfl⟩
  | inr e =>
    have he : e = d := by
      apply Fin.ext
      have hd := d.isLt
      have he := e.isLt
      have hh := Nat.mod_lt (Fintype.card V) (by omega : 0 < 2)
      omega
    subst e
    exact False.elim (p.apply_ne _ h)

lemma oldProject_surjective {V : Type cycleUniverse43} [Fintype V] (p : PairingSpace V) :
    Function.Surjective (oldProject p) := by
  intro q
  obtain ⟨x,rfl⟩ := p.project_surjective q
  cases x with
  | inl v => exact ⟨v,rfl⟩
  | inr d =>
    obtain ⟨v,hv⟩ := dummy_partner_is_old p d
    refine ⟨v,?_⟩
    change p.project (Sum.inl v) = p.project (Sum.inr d)
    rw [← hv,p.project_apply]

lemma old_quotient_order {V : Type cycleUniverse44} [Fintype V] (p : PairingSpace V) :
    Fintype.card (Pairing.PairQuotient p) = Fintype.card V - Fintype.card V / 2 := by
  have h := p.card_pairQuotient
  simp only [Fintype.card_sum,Fintype.card_fin] at h
  omega

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section

variable {V : Type cycleUniverse46} {I : Type cycleUniverse47} [Fintype V] [Fintype I] (X : I → Finset V)

lemma familyProject_surjective (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) : Function.Surjective (familyProject X hd p) := by
  have h : Function.Surjective (foldOnDomain X p) := by
    rintro (v | ⟨i,q⟩)
    · exact ⟨Sum.inl v,rfl⟩
    · obtain ⟨v,hv⟩ := oldProject_surjective (p i) q
      exact ⟨Sum.inr ⟨i,v⟩,by simp only [foldOnDomain,hv]⟩
  exact h.comp (splitEquiv X hd).symm.surjective

lemma family_quotient_order_add (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) :
    Fintype.card (FamilyQuotient X p) + ∑ i, (X i).card / 2 = Fintype.card V := by
  classical
  have hV := Fintype.card_congr (splitEquiv X hd)
  have hV' : Fintype.card (Outside X) + ∑ i, (X i).card = Fintype.card V := by
    simpa only [FoldDomain,Fintype.card_sum,Fintype.card_sigma,Fintype.card_coe] using hV
  rw [Fintype.card_sum,Fintype.card_sigma,add_assoc,← Finset.sum_add_distrib]
  simp_rw [old_quotient_order,Fintype.card_coe,Nat.sub_add_cancel (Nat.div_le_self _ _)]
  exact hV'

theorem family_quotient_order (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) :
    Fintype.card (FamilyQuotient X p) = Fintype.card V - ∑ i, (X i).card / 2 := by
  have h := family_quotient_order_add X hd p
  omega

lemma familyProject_eq_on_inside (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (i : I) (v : X i) :
    familyProject X hd p v.val = Sum.inr ⟨i,oldProject (p i) v⟩ := by
  have hv : (splitEquiv X hd) (Sum.inr ⟨i,v⟩) = v.val := rfl
  rw [familyProject,Function.comp_apply,← hv,Equiv.symm_apply_apply]
  rfl

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse50} {I : Type cycleUniverse51} [Fintype V] [Fintype I] (X : I → Finset V)

lemma familyProject_apply_split (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (x : FoldDomain X) :
    familyProject X hd p ((splitEquiv X hd) x) = foldOnDomain X p x := by
  simp only [familyProject,Function.comp_apply,Equiv.symm_apply_apply]

lemma familyProject_eq_iff (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (u v : V) :
    familyProject X hd p u = familyProject X hd p v ↔ u = v ∨ familyPaired X p u v := by
  constructor
  · intro h
    obtain ⟨a,rfl⟩ := (splitEquiv X hd).surjective u
    obtain ⟨b,rfl⟩ := (splitEquiv X hd).surjective v
    rw [familyProject_apply_split,familyProject_apply_split] at h
    rcases a with a | ⟨i,a⟩ <;> rcases b with b | ⟨j,b⟩
    · exact Or.inl (congrArg (splitEquiv X hd) (congrArg Sum.inl (Sum.inl.inj h)))
    · simp only [foldOnDomain,Sum.inl_ne_inr] at h
    · simp only [foldOnDomain,Sum.inr_ne_inl] at h
    · have hh := Sum.inr.inj h
      have hij := congrArg Sigma.fst hh
      change i = j at hij
      subst j
      have hval : oldProject (p i) a = oldProject (p i) b := by
        simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
      obtain hab | hab := (oldProject_eq_iff (p i) a b).mp hval
      · subst b
        exact Or.inl rfl
      · exact Or.inr ⟨i,a.property,b.property,hab⟩
  · rintro (rfl | ⟨i,hu,hv,hp⟩)
    · rfl
    · rw [familyProject_eq_on_inside X hd p i ⟨u,hu⟩,
        familyProject_eq_on_inside X hd p i ⟨v,hv⟩]
      congr 2
      exact (oldProject_eq_iff (p i) ⟨u,hu⟩ ⟨v,hv⟩).mpr (Or.inr hp)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse56} {I : Type cycleUniverse57} [Fintype V] [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (p : ∀ i, PairingSpace (X i))

lemma loop_iff_familyPaired {u v : V} (huv : u ≠ v) :
    (Sym2.map (familyProject X hd p) s(u,v)).IsDiag ↔ familyPaired X p u v := by
  simp only [Sym2.map_mk,Sym2.mk_isDiag_iff,
    familyProject_eq_iff,huv,false_or]

lemma shared_endpoint_collision {v u w : V} (huw : u ≠ w)
    (h : Sym2.map (familyProject X hd p) s(v,u) =
      Sym2.map (familyProject X hd p) s(v,w)) : familyPaired X p u w := by
  have h := (Sym2.mk_eq_mk_iff (p := (familyProject X hd p v, familyProject X hd p u))
    (q := (familyProject X hd p v, familyProject X hd p w))).mp h
  simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h
  have he : familyProject X hd p u = familyProject X hd p w := by
    rcases h with h | h
    · exact h.2
    · exact h.2.trans h.1
  exact ((familyProject_eq_iff X hd p u w).mp he).resolve_left huw

lemma four_endpoint_collision {u v x y : V}
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (h : Sym2.map (familyProject X hd p) s(u,v) =
      Sym2.map (familyProject X hd p) s(x,y)) :
    (familyPaired X p u x ∧ familyPaired X p v y) ∨
    (familyPaired X p u y ∧ familyPaired X p v x) := by
  have h := (Sym2.mk_eq_mk_iff (p := (familyProject X hd p u, familyProject X hd p v))
    (q := (familyProject X hd p x, familyProject X hd p y))).mp h
  simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h
  rcases h with h | h
  · exact Or.inl ⟨((familyProject_eq_iff X hd p u x).mp h.1).resolve_left hux,
      ((familyProject_eq_iff X hd p v y).mp h.2).resolve_left hvy⟩
  · exact Or.inr ⟨((familyProject_eq_iff X hd p u y).mp h.1).resolve_left huy,
      ((familyProject_eq_iff X hd p v x).mp h.2).resolve_left hvx⟩

lemma paired_fibers_placement {V : Type cycleUniverse58} {I : Type cycleUniverse59} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (p : (i : I) → ErdosGallai.Batch.PairingSpace (Subtype fun x => x ∈ X i)) {u v x y : V}
    (hux : familyPaired X p u x) (hvy : familyPaired X p v y) :
    (∃ i, u ∈ X i ∧ v ∈ X i ∧ x ∈ X i ∧ y ∈ X i) ∨
    (∃ i j, i ≠ j ∧ u ∈ X i ∧ x ∈ X i ∧ v ∈ X j ∧ y ∈ X j) := by
  obtain ⟨i,hu,hx,_⟩ := hux
  obtain ⟨j,hv,hy,_⟩ := hvy
  by_cases hij : i = j
  · subst j
    exact Or.inl ⟨i,hu,hv,hx,hy⟩
  · exact Or.inr ⟨i,j,hij,hu,hx,hv,hy⟩

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CollisionEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse1} [Fintype V] (G : SimpleGraph V)

lemma neighborsIn_le_degree (X : Finset V) (v : V) :
    neighborsIn G X v ≤ G.degree v := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2

lemma neighborsIn_eq_sum {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] (G : SimpleGraph V) (X : Finset V) (v : V) :
    neighborsIn G X v = ∑ x ∈ X, if G.Adj v x then 1 else 0 := by
  classical
  simp only [neighborsIn,Finset.card_eq_sum_ones,Finset.sum_filter]

lemma sum_incidence_to_set (X : Finset V) :
    ∑ v, neighborsIn G X v = ∑ x ∈ X, G.degree x := by
  classical
  simp_rw [neighborsIn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [G.adj_comm (v:=x)]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj x) = G.neighborFinset x := by
    ext y
    simp
  simp [he]

lemma internalGraph_degree (X : Finset V) (v : V) :
    (internalGraph G X).degree v = if v ∈ X then neighborsIn G X v else 0 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : v ∈ X
  · simp only [hv,ite_true]
    congr 1
    ext x
    rw [SimpleGraph.mem_neighborFinset,Finset.mem_filter]
    change (G.Adj v x ∧ v ∈ X ∧ x ∈ X) ↔ _
    tauto
  · have he : (internalGraph G X).neighborFinset v = ∅ := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset,Finset.notMem_empty]
      change (G.Adj v x ∧ v ∈ X ∧ x ∈ X) ↔ False
      tauto
    simp [he,hv]

lemma internalGraph_degree_sum (X : Finset V) :
    2 * (internalGraph G X).edgeFinset.card = ∑ x ∈ X, neighborsIn G X x := by
  classical
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp_rw [internalGraph_degree]
  simp

lemma internal_edge_bound (X : Finset V) (a : ℝ)
    (ha : ∀ x ∈ X, (G.degree x : ℝ) ≤ a) :
    2 * ((internalGraph G X).edgeFinset.card : ℝ) ≤ a * X.card := by
  have hid := congrArg (fun n : ℕ => (n:ℝ)) (internalGraph_degree_sum G X)
  push_cast at hid
  rw [hid]
  calc
    _ ≤ ∑ x ∈ X, a := Finset.sum_le_sum fun x hx =>
      (Nat.cast_le.mpr (neighborsIn_le_degree G X x)).trans (ha x hx)
    _ = _ := by simp [mul_comm]

lemma incidence_bound (X : Finset V) (a : ℝ)
    (ha : ∀ x ∈ X, (G.degree x : ℝ) ≤ a) :
    (∑ v, neighborsIn G X v : ℝ) ≤ a * X.card := by
  have hid := congrArg (fun n : ℕ => (n:ℝ)) (sum_incidence_to_set G X)
  push_cast at hid
  rw [hid]
  simpa [mul_comm] using Finset.sum_le_sum (s:=X) (fun x hx => ha x hx)

lemma wedge_count_bound (X : Finset V) (a : ℝ) (ha : 1 ≤ a)
    (hdegree : ∀ x ∈ X, (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ v, (neighborsIn G X v : ℝ) ≤ a) :
    ((∑ v, (neighborsIn G X v).choose 2 : ℕ) : ℝ) ≤
      a*(a-1)*X.card/2 := by
  have hb (v : V) : ((neighborsIn G X v).choose 2 : ℝ) ≤
      (a-1)*(neighborsIn G X v)/2 := by
    rw [Nat.cast_choose_two]
    have hn : (0:ℝ) ≤ neighborsIn G X v := Nat.cast_nonneg _
    have hn' := hneighbor v
    nlinarith
  calc
    _ = ∑ v, ((neighborsIn G X v).choose 2 : ℝ) := by push_cast; rfl
    _ ≤ ∑ v, (a-1)*(neighborsIn G X v)/2 := Finset.sum_le_sum fun v _ => hb v
    _ = (a-1)/2 * ∑ v, (neighborsIn G X v : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (a-1)/2 * (a*X.card) := mul_le_mul_of_nonneg_left
        (incidence_bound G X a hdegree) (by positivity)
    _ = _ := by ring

lemma betweenCount_comm (X Y : Finset V) :
    betweenCount G X Y = betweenCount G Y X := by
  classical
  simp only [betweenCount,neighborsIn_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  simp only [G.adj_comm]

lemma betweenCount_bound (X Y : Finset V) (a : ℝ)
    (hdegree : ∀ y ∈ Y, (G.degree y : ℝ) ≤ a) :
    (betweenCount G X Y : ℝ) ≤ a*Y.card := by
  rw [betweenCount_comm]
  simp only [betweenCount,Nat.cast_sum]
  calc
    _ ≤ ∑ y ∈ Y, a := Finset.sum_le_sum fun y hy =>
      (Nat.cast_le.mpr (neighborsIn_le_degree G X y)).trans (hdegree y hy)
    _ = _ := by simp [mul_comm]

lemma disjoint_neighbor_sum_le {I : Type cycleUniverse3} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (v : V) :
    ∑ i, neighborsIn G (X i) v ≤ G.degree v := by
  classical
  have hb : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (X i).filter (G.Adj v)) := by
    intro i hi j hj hij
    exact (hd hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  simp only [neighborsIn]
  rw [← Finset.card_biUnion hb,← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2

lemma betweenCount_row_bound {I : Type cycleUniverse4} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (i : I) (a : ℝ)
    (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a) :
    (∑ j, betweenCount G (X i) (X j) : ℝ) ≤ a*(X i).card := by
  simp only [betweenCount,Nat.cast_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x ∈ X i, a := by
      apply Finset.sum_le_sum
      intro x hx
      have hn := disjoint_neighbor_sum_le G X hd x
      have hn' : (∑ j, (neighborsIn G (X j) x : ℝ)) ≤ G.degree x := by
        exact_mod_cast hn
      exact hn'.trans (hdegree x hx)
    _ = _ := by simp [mul_comm]

lemma cross_error_row {I : Type cycleUniverse5} [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 0 ≤ a)
    (hsize : ∀ i, 0 < (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a) (i : I) :
    (∑ j, ((betweenCount G (X i) (X j) : ℝ)^2 /
      ((X i).card*(X j).card))) ≤ a^2 := by
  have hmi : (0:ℝ) < (X i).card := by exact_mod_cast hsize i
  calc
    _ ≤ ∑ j, a/(X i).card * (betweenCount G (X i) (X j) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hmj : (0:ℝ) < (X j).card := by exact_mod_cast hsize j
      have he := betweenCount_bound G (X i) (X j) a (hdegree j)
      have hn : (0:ℝ) ≤ betweenCount G (X i) (X j) := Nat.cast_nonneg _
      apply (div_le_iff₀ (mul_pos hmi hmj)).mpr
      field_simp
      nlinarith
    _ = a/(X i).card * ∑ j, (betweenCount G (X i) (X j) : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ a/(X i).card * (a*(X i).card) := mul_le_mul_of_nonneg_left
      (betweenCount_row_bound G X hd i a (hdegree i)) (by positivity)
    _ = a^2 := by field_simp

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section

lemma mem_collisionPairs {α : Type cycleUniverse8} {β : Type cycleUniverse9} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (p : Finset α) :
    p ∈ CollisionPairs f s ↔ p ⊆ s ∧ p.card = 2 ∧ (p.image f).card = 1 := by
  classical
  simp [CollisionPairs,and_assoc]

lemma collisionPairs_mono {α : Type cycleUniverse10} {β : Type cycleUniverse11} [DecidableEq α] [DecidableEq β] (f : α → β) {s t : Finset α} (h : s ⊆ t) :
    CollisionPairs f s ⊆ CollisionPairs f t := by
  classical
  intro p hp
  rw [mem_collisionPairs] at hp ⊢
  exact ⟨hp.1.trans h,hp.2⟩

lemma pair_mem_collisionPairs {α : Type cycleUniverse12} {β : Type cycleUniverse13} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) (heq : f a = f b) :
    {a,b} ∈ CollisionPairs f s := by
  classical
  rw [mem_collisionPairs]
  refine ⟨?_,by simp [hne],by simp [heq]⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ha
  · exact Finset.mem_singleton.mp hx ▸ hb

theorem prune_collisions {α : Type cycleUniverse14} {β : Type cycleUniverse15} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) :
    ∃ t ⊆ s, Set.InjOn f (t : Set α) ∧ t.image f = s.image f ∧
      s.card - t.card ≤ (CollisionPairs f s).card := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hinj : Set.InjOn f (s : Set α)
  · exact ⟨s,Subset.rfl,hinj,rfl,by simp⟩
  simp only [Set.InjOn,Finset.mem_coe,not_forall] at hinj
  obtain ⟨a,ha,b,hb,heq,hne⟩ := hinj
  have hsub : s.erase a ⊂ s := Finset.erase_ssubset ha
  obtain ⟨t,ht,hinj,himage,hcost⟩ := ih (s.erase a) hsub
  have hpair := pair_mem_collisionPairs f s ha hb hne heq
  have hnot : ({a,b}:Finset α) ∉ CollisionPairs f (s.erase a) := by
    intro hp
    have hh := (mem_collisionPairs f _ _).mp hp
    have := hh.1 (show a ∈ ({a,b}:Finset α) by simp)
    simp at this
  have hlt : (CollisionPairs f (s.erase a)).card < (CollisionPairs f s).card := by
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨collisionPairs_mono f (Finset.erase_subset _ _),
      fun he => hnot (he ▸ hpair)⟩
  have himage' : (s.erase a).image f = s.image f := by
    apply le_antisymm
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      by_cases hxa : x = a
      · subst x
        exact Finset.mem_image.mpr ⟨b,by simp [hb,Ne.symm hne],heq.symm⟩
      · exact Finset.mem_image.mpr ⟨x,by simp [hx,hxa],rfl⟩
  refine ⟨t,ht.trans (Finset.erase_subset _ _),hinj,himage.trans himage',?_⟩
  have hcard := Finset.card_erase_of_mem ha
  have htt := Finset.card_le_card ht
  omega

theorem prune_bad_images {α : Type cycleUniverse16} {β : Type cycleUniverse17} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (bad : β → Prop) [DecidablePred bad] :
    ∃ t ⊆ s, (∀ x ∈ t, ¬ bad (f x)) ∧ Set.InjOn f (t : Set α) ∧
      t.image f = (s.filter (fun x => ¬bad (f x))).image f ∧
      s.card-t.card ≤ (s.filter (fun x => bad (f x))).card +
        (CollisionPairs f (s.filter (fun x => ¬bad (f x)))).card := by
  classical
  obtain ⟨t,ht,hinj,himage,hcost⟩ := prune_collisions f (s.filter (fun x => ¬bad (f x)))
  refine ⟨t,ht.trans (Finset.filter_subset _ _),?_,hinj,himage,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp (ht hx)).2
  · have hpart := Finset.card_filter_add_card_filter_not (s:=s) (p:=fun x => bad (f x))
    have hle := Finset.card_le_card ht
    omega

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem simple_quotient_representatives {V : Type cycleUniverse20} {W : Type cycleUniverse21} [Fintype V]
    (G : SimpleGraph V) (projMap : V → W) :
    ∃ (retained : Finset (Sym2 V)) (Q : SimpleGraph W),
      retained ⊆ G.edgeFinset ∧
      (G.edgeFinset \ retained).card ≤ quotientDefect G projMap ∧
      Q.edgeSet = ((retained.image (Sym2.map projMap) : Finset (Sym2 W)) : Set (Sym2 W)) ∧
      (∀ e ∈ Q.edgeSet, ∃! f, f ∈ retained ∧ Sym2.map projMap f = e) := by
  classical
  obtain ⟨t,ht,hgood,hinj,himage,hcost⟩ :=
    prune_bad_images (Sym2.map projMap) G.edgeFinset Sym2.IsDiag
  let Q : SimpleGraph W := SimpleGraph.fromEdgeSet (t.image (Sym2.map projMap) : Set (Sym2 W))
  have hQ : Q.edgeSet = (t.image (Sym2.map projMap) : Set (Sym2 W)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact fun h => h.1
    · intro he
      refine ⟨he,?_⟩
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      exact hgood f hf
  refine ⟨t,Q,ht,?_,hQ,?_⟩
  · rw [Finset.card_sdiff_of_subset ht]
    exact hcost
  · intro e he
    rw [hQ] at he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp he
    refine ⟨f,⟨hf,hfe⟩,?_⟩
    intro g hg
    exact hinj hg.1 hf (hg.2.trans hfe.symm)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse22} {I : Type cycleUniverse23} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma familyPaired_symm {V : Type cycleUniverse24} {I : Type cycleUniverse25} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (p : ∀ i, PairingSpace (X i)) {u v : V}
    (h : familyPaired X p u v) : familyPaired X p v u := by
  obtain ⟨i,hu,hv,hp⟩ := h
  exact ⟨i,hv,hu,paired_symm (p i) hp⟩

lemma familyPaired_local {V : Type cycleUniverse26} {I : Type cycleUniverse27} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j)) (p : ∀ i, PairingSpace (X i)) (i : I)
    (u v : X i) : familyPaired X p u v ↔ paired (p i) u v := by
  constructor
  · rintro ⟨j,hu,hv,hp⟩
    have hij : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hd hij) u.property hu
    subst j
    exact hp
  · intro hp
    exact ⟨i,u.property,v.property,hp⟩

lemma familyPaired_same_set {V : Type cycleUniverse28} {I : Type cycleUniverse29} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j)) (p : ∀ i, PairingSpace (X i)) (i : I)
    {u v : V} (hu : u ∈ X i) (hp : familyPaired X p u v) : v ∈ X i := by
  obtain ⟨j,hu',hv,hp⟩ := hp
  have hij : i = j := by
    by_contra hij
    exact Finset.disjoint_left.mp (hd hij) hu hu'
  exact hij.symm ▸ hv

lemma vertexPairEvent_pair (p : ∀ i, PairingSpace (X i)) (u v : V) (huv : u ≠ v) :
    vertexPairEvent X p {u,v} ↔ familyPaired X p u v := by
  constructor
  · rintro ⟨a,ha,b,hb,hab,hp⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hp
    · exact familyPaired_symm X p hp
    · exact False.elim (hab rfl)
  · intro hp
    exact ⟨u,by simp,v,by simp,huv,hp⟩

lemma finiteAverage_filter_card {Ω : Type cycleUniverse30} {A : Type cycleUniverse31} [Fintype Ω]
    (s : Finset A) (P : Ω → A → Prop) :
    finiteAverage (fun ω => ((s.filter (P ω)).card : ℝ)) =
      ∑ a ∈ s, finiteAverage (fun ω => if P ω a then 1 else 0) := by
  have hf (ω : Ω) : ((s.filter (P ω)).card : ℝ) =
      ∑ a ∈ s, if P ω a then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one,Finset.sum_filter]
  simp_rw [hf]
  exact finiteAverage_sum s _

include hd in
lemma vertexPairEvent_average (i : I) (s : Finset V)
    (hs : s ⊆ X i) (hc : s.card = 2) (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if vertexPairEvent X p s then 1 else 0) ≤ 1 / ((X i).card-1:ℝ) := by
  classical
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp hc
  have hu := hs (show u ∈ ({u,v}:Finset V) by simp)
  have hv := hs (show v ∈ ({u,v}:Finset V) by simp)
  have he (p : ∀ j, PairingSpace (X j)) :
      vertexPairEvent X p {u,v} ↔ paired (p i) ⟨u,hu⟩ ⟨v,hv⟩ :=
    (vertexPairEvent_pair X p u v huv).trans (familyPaired_local X hd p i ⟨u,hu⟩ ⟨v,hv⟩)
  simp_rw [he]
  rw [finiteAverage_pi_eval (Ω:=fun j => PairingSpace (X j)) i
    (fun p => if paired p ⟨u,hu⟩ ⟨v,hv⟩ then 1 else 0)]
  convert paired_first_bound (V:=(X i)) (by simpa using hm) ⟨u,hu⟩ ⟨v,hv⟩
    (fun h => huv (congrArg Subtype.val h)) using 1 ; simp

include hd in
lemma wedgeErrors_average (G : SimpleGraph V) (i : I) (v : V)
    (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) => ((wedgeErrors X G p i v).card : ℝ)) ≤
      ((neighborsIn G (X i) v).choose 2 : ℝ) / ((X i).card-1:ℝ) := by
  classical
  change finiteAverage (fun p => (((((X i).filter (G.Adj v)).powersetCard 2).filter
    (vertexPairEvent X p)).card : ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _s ∈ ((X i).filter (G.Adj v)).powersetCard 2,
        1 / ((X i).card-1:ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hs
      exact vertexPairEvent_average X hd i s (hs.trans (Finset.filter_subset _ _)) hc hm
    _ = _ := by simp [Finset.card_powersetCard,neighborsIn,div_eq_mul_inv]

lemma mem_internalGraph {G : SimpleGraph V} {S : Finset V} {u v : V} :
    s(u,v) ∈ (internalGraph G S).edgeFinset ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  rfl

lemma distinct_edge_cases (G : SimpleGraph V) {e f : Sym2 V}
    (he : e ∈ G.edgeFinset) (hf : f ∈ G.edgeFinset) (hef : e ≠ f) :
    (∃ v u w, v ≠ u ∧ v ≠ w ∧ u ≠ w ∧ e = s(v,u) ∧ f = s(v,w)) ∨
    (∃ u v x y, u ≠ v ∧ x ≠ y ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
      e = s(u,v) ∧ f = s(x,y)) := by
  obtain ⟨a,b⟩ := e
  obtain ⟨c,d⟩ := f
  have hab : a ≠ b := (SimpleGraph.mem_edgeFinset.mp he).ne
  have hcd : c ≠ d := (SimpleGraph.mem_edgeFinset.mp hf).ne
  by_cases hac : a = c
  · subst c
    refine Or.inl ⟨a,b,d,hab,hcd,?_,rfl,rfl⟩
    intro hbd
    exact hef (hbd ▸ rfl)
  by_cases had : a = d
  · subst d
    refine Or.inl ⟨a,b,c,hab,hcd.symm,?_,rfl,Sym2.eq_swap⟩
    intro hbc
    subst c
    exact hef Sym2.eq_swap
  by_cases hbc : b = c
  · subst c
    refine Or.inl ⟨b,a,d,hab.symm,hcd,?_,Sym2.eq_swap,rfl⟩
    intro had
    subst d
    exact hef Sym2.eq_swap
  by_cases hbd : b = d
  · subst d
    refine Or.inl ⟨b,a,c,hab.symm,hcd.symm,?_,Sym2.eq_swap,Sym2.eq_swap⟩
    intro hac
    subst c
    exact hef rfl
  exact Or.inr ⟨a,b,c,d,hab,hcd,hac,had,hbc,hbd,rfl,rfl⟩

lemma internal_collision_average (i : I) (hm : 4 ≤ (X i).card)
    (u v x y : X i) (huv : u ≠ v) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ)) := by
  classical
  have hmono : finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      if (paired (p i) u x ∧ paired (p i) v y) ∨
        (paired (p i) u y ∧ paired (p i) v x) then 1 else 0) := by
    apply finiteAverage_mono
    intro p
    by_cases hc : Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V))
    · have hh := four_endpoint_collision X hd p (fun h => hux (Subtype.ext h))
        (fun h => huy (Subtype.ext h)) (fun h => hvx (Subtype.ext h))
        (fun h => hvy (Subtype.ext h)) hc
      have he : (paired (p i) u x ∧ paired (p i) v y) ∨
          (paired (p i) u y ∧ paired (p i) v x) := by
        simpa only [familyPaired_local X hd p i] using hh
      simp only [ite_eq_left hc,ite_eq_left he,le_refl]
    · rw [ite_eq_right hc]
      split_ifs <;> norm_num
  apply hmono.trans
  rw [finiteAverage_pi_eval (Ω:=fun j => PairingSpace (X j)) i
    (fun p => if (paired p u x ∧ paired p v y) ∨ (paired p u y ∧ paired p v x)
      then 1 else 0)]
  simpa only [Fintype.card_coe] using pairing_patterns_internal
    (V:=(X i)) (by simpa using hm) u v x y huv hux huy hvx hvy hxy

lemma cross_collision_average (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ (X i).card) (hj : 2 ≤ (X j).card)
    (u x : X i) (v y : X j) (hux : u ≠ x) (hvy : v ≠ y) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ)) := by
  classical
  have huy : (u:V) ≠ y := by
    intro h
    exact Finset.disjoint_left.mp (hd hij) u.property (h ▸ y.property)
  have hvx : (v:V) ≠ x := by
    intro h
    exact Finset.disjoint_left.mp (hd hij) (h ▸ x.property) v.property
  have hmono : finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V)) then 1 else 0) ≤
      finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      if paired (p i) u x ∧ paired (p j) v y then 1 else 0) := by
    apply finiteAverage_mono
    intro p
    by_cases hc : Sym2.map (familyProject X hd p) s((u:V),(v:V)) =
         Sym2.map (familyProject X hd p) s((x:V),(y:V))
    · have hh := four_endpoint_collision X hd p (fun h => hux (Subtype.ext h))
        huy hvx (fun h => hvy (Subtype.ext h)) hc
      have he : paired (p i) u x ∧ paired (p j) v y := by
        rcases hh with hh | hh
        · exact ⟨(familyPaired_local X hd p i u x).mp hh.1,
            (familyPaired_local X hd p j v y).mp hh.2⟩
        · have hy := familyPaired_same_set X hd p i u.property hh.1
          exact False.elim (Finset.disjoint_left.mp (hd hij) hy y.property)
      simp only [ite_eq_left hc,ite_eq_left he,le_refl]
    · rw [ite_eq_right hc]
      split_ifs <;> norm_num
  apply hmono.trans
  simpa only [Fintype.card_coe] using pairing_patterns_cross_bound
    (V:=fun k => X k) i j hij (by simpa using hi) (by simpa using hj) u x hux v y hvy

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma crossGraph_card (G : SimpleGraph V) (S T : Finset V) (hst : Disjoint S T) :
    (crossGraph G S T).edgeFinset.card = betweenCount G S T := by
  classical
  have hdeg (v : V) : (crossGraph G S T).degree v =
      (if v ∈ S then neighborsIn G T v else 0) +
      (if v ∈ T then neighborsIn G S v else 0) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hfin : (crossGraph G S T).neighborFinset v =
      (if v ∈ S then T.filter (G.Adj v) else ∅) ∪
      (if v ∈ T then S.filter (G.Adj v) else ∅) := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union]
      change (G.Adj v x ∧ ((v ∈ S ∧ x ∈ T) ∨ (v ∈ T ∧ x ∈ S))) ↔ _
      split_ifs <;> simp_all only [Finset.mem_filter,Finset.notMem_empty] <;> tauto
    rw [hfin,Finset.card_union_of_disjoint]
    · split_ifs <;> simp [neighborsIn]
    · split_ifs with hs ht ht
      · exact False.elim (Finset.disjoint_left.mp hst hs ht)
      all_goals simp
  have hh := (crossGraph G S T).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hh
  rw [Finset.sum_add_distrib] at hh
  have hS : (∑ v, if v ∈ S then neighborsIn G T v else 0) = betweenCount G S T := by
    simp [betweenCount]
  have hT : (∑ v, if v ∈ T then neighborsIn G S v else 0) = betweenCount G T S := by
    simp [betweenCount]
  rw [hS,hT,betweenCount_comm G T S] at hh
  omega

lemma edgePairEvent_pair (p : ∀ i, PairingSpace (X i)) (e f : Sym2 V) :
    edgePairEvent X hd p {e,f} ↔
      Sym2.map (familyProject X hd p) e = Sym2.map (familyProject X hd p) f := by
  classical
  by_cases h : Sym2.map (familyProject X hd p) e = Sym2.map (familyProject X hd p) f
  · simp [edgePairEvent,h]
  · simp [edgePairEvent,h,Finset.card_pair h]

lemma loopErrors_average (G : SimpleGraph V) (i : I) (hm : 2 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) => ((loopErrors X hd G p i).card : ℝ)) ≤
      ((internalGraph G (X i)).edgeFinset.card : ℝ) / ((X i).card-1:ℝ) := by
  classical
  change finiteAverage (fun p => (((internalGraph G (X i)).edgeFinset.filter _).card:ℝ)) ≤ _
  have hav := finiteAverage_filter_card (s:=(internalGraph G (X i)).edgeFinset)
    (P:=fun (p : ∀ j, PairingSpace (X j)) e => (Sym2.map (familyProject X hd p) e).IsDiag)
  calc
    _ = ∑ e ∈ (internalGraph G (X i)).edgeFinset,
        finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
          if (Sym2.map (familyProject X hd p) e).IsDiag then 1 else 0) := by
      convert hav using 1 <;> congr 4
      · funext p
        congr 2
        ext e
        simp only [Finset.mem_filter]
      · funext e
        congr 1
        funext p
        split_ifs <;> rfl
    _ ≤ _ := by
      calc
        _ ≤ ∑ _e ∈ (internalGraph G (X i)).edgeFinset, 1 / ((X i).card-1:ℝ) := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨u,v⟩ := e
          obtain ⟨huv,hu,hv⟩ := mem_internalGraph.mp he
          have heq (p : ∀ j, PairingSpace (X j)) :
              (Sym2.map (familyProject X hd p) s(u,v)).IsDiag ↔ vertexPairEvent X p {u,v} :=
            (loop_iff_familyPaired X hd p huv.ne).trans (vertexPairEvent_pair X p u v huv.ne).symm
          simp_rw [heq]
          exact vertexPairEvent_average X hd i {u,v} (by intro z hz; rcases Finset.mem_insert.mp hz with rfl | hz; exact hu; exact Finset.mem_singleton.mp hz ▸ hv)
            (by simp [huv.ne]) hm
        _ = _ := by simp [div_eq_mul_inv]

lemma internal_pairErrors_average (G : SimpleGraph V) (i : I) (hm : 4 ≤ (X i).card) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((pairErrors X hd (internalGraph G (X i)) p).card : ℝ)) ≤
      ((internalGraph G (X i)).edgeFinset.card.choose 2 : ℝ) *
        (2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ))) := by
  classical
  change finiteAverage (fun p => (((((internalGraph G (X i)).edgeFinset.powersetCard 2).filter DisjointEdgePair).filter _).card:ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _q ∈ ((internalGraph G (X i)).edgeFinset.powersetCard 2).filter DisjointEdgePair,
        2 / (((X i).card-1:ℝ)*((X i).card-3:ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq,hdis⟩ := Finset.mem_filter.mp hq
      obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩ := hdis
      have hsub := (Finset.mem_powersetCard.mp hq).1
      obtain ⟨he,hu,hv⟩ := mem_internalGraph.mp (hsub (by simp : s(u,v) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
      obtain ⟨hf,hx,hy⟩ := mem_internalGraph.mp (hsub (by simp : s(x,y) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
      simp_rw [edgePairEvent_pair]
      exact internal_collision_average X hd i hm ⟨u,hu⟩ ⟨v,hv⟩ ⟨x,hx⟩ ⟨y,hy⟩
        (fun h => huv (congrArg Subtype.val h)) (fun h => hux (congrArg Subtype.val h))
        (fun h => huy (congrArg Subtype.val h)) (fun h => hvx (congrArg Subtype.val h))
        (fun h => hvy (congrArg Subtype.val h)) (fun h => hxy (congrArg Subtype.val h))
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard _ _)
      · have : (4:ℝ) ≤ (X i).card := by exact_mod_cast hm
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

lemma cross_pair_orientation {V : Type cycleUniverse3} {I : Type cycleUniverse4} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (G : SimpleGraph V) (i j : I)
    (q : Finset (Sym2 V)) (hq : q ⊆ (crossGraph G (X i) (X j)).edgeFinset)
    (hdis : DisjointEdgePair q) :
    ∃ (u x : X i) (v y : X j), u ≠ x ∧ v ≠ y ∧ q = {s((u:V),(v:V)),s((x:V),(y:V))} := by
  classical
  obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩ := hdis
  have he := SimpleGraph.mem_edgeFinset.mp (hq (by simp : s(u,v) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
  have hf := SimpleGraph.mem_edgeFinset.mp (hq (by simp : s(x,y) ∈ ({s(u,v),s(x,y)}:Finset (Sym2 V))))
  rcases he.2 with ⟨hui,hvj⟩ | ⟨huj,hvi⟩ <;> rcases hf.2 with ⟨hxi,hyj⟩ | ⟨hxj,hyi⟩
  · exact ⟨⟨u,hui⟩,⟨x,hxi⟩,⟨v,hvj⟩,⟨y,hyj⟩,
      (fun h => hux (congrArg Subtype.val h)),(fun h => hvy (congrArg Subtype.val h)),rfl⟩
  · refine ⟨⟨u,hui⟩,⟨y,hyi⟩,⟨v,hvj⟩,⟨x,hxj⟩,
      (fun h => huy (congrArg Subtype.val h)),(fun h => hvx (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=y) (b:=x)]
  · refine ⟨⟨v,hvi⟩,⟨x,hxi⟩,⟨u,huj⟩,⟨y,hyj⟩,
      (fun h => hvx (congrArg Subtype.val h)),(fun h => huy (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=v) (b:=u)]
  · refine ⟨⟨v,hvi⟩,⟨y,hyi⟩,⟨u,huj⟩,⟨x,hxj⟩,
      (fun h => hvy (congrArg Subtype.val h)),(fun h => hux (congrArg Subtype.val h)),?_⟩
    rw [Sym2.eq_swap (a:=v) (b:=u),Sym2.eq_swap (a:=y) (b:=x)]

lemma cross_pairErrors_average (G : SimpleGraph V) (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ (X i).card) (hj : 2 ≤ (X j).card) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      ((pairErrors X hd (crossGraph G (X i) (X j)) p).card : ℝ)) ≤
      ((betweenCount G (X i) (X j)).choose 2 : ℝ) *
        (1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ))) := by
  classical
  change finiteAverage (fun p => (((((crossGraph G (X i) (X j)).edgeFinset.powersetCard 2).filter DisjointEdgePair).filter _).card:ℝ)) ≤ _
  rw [finiteAverage_filter_card]
  calc
    _ ≤ ∑ _q ∈ ((crossGraph G (X i) (X j)).edgeFinset.powersetCard 2).filter DisjointEdgePair,
        1 / (((X i).card-1:ℝ)*((X j).card-1:ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq,hdis⟩ := Finset.mem_filter.mp hq
      obtain ⟨u,x,v,y,hux,hvy,rfl⟩ := cross_pair_orientation X G i j q
        (Finset.mem_powersetCard.mp hq).1 hdis
      simp_rw [edgePairEvent_pair]
      exact cross_collision_average X hd i j hij hi hj u x v y hux hvy
    _ ≤ _ := by
      rw [← crossGraph_card G (X i) (X j) (hd hij)]
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard _ _)
      · have : (2:ℝ) ≤ (X i).card := by exact_mod_cast hi
        have : (2:ℝ) ≤ (X j).card := by exact_mod_cast hj
        exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse5} {I : Type cycleUniverse6} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma mem_pairErrors (H : SimpleGraph V) (p : ∀ i, PairingSpace (X i))
    (q : Finset (Sym2 V)) :
    q ∈ pairErrors X hd H p ↔ q ⊆ H.edgeFinset ∧ q.card = 2 ∧
      DisjointEdgePair q ∧ edgePairEvent X hd p q := by
  classical
  simp [pairErrors,and_assoc]

lemma mem_crossGraph {G : SimpleGraph V} {S T : Finset V} {u v : V} :
    s(u,v) ∈ (crossGraph G S T).edgeFinset ↔
      G.Adj u v ∧ ((u ∈ S ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ S)) := by
  rw [SimpleGraph.mem_edgeFinset]
  rfl

lemma two_paired_edges_placement (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i))
    {u v x y : V} (he : G.Adj u v) (hf : G.Adj x y)
    (hux : familyPaired X p u x) (hvy : familyPaired X p v y) :
    (∃ i, {s(u,v),s(x,y)} ⊆ (internalGraph G (X i)).edgeFinset) ∨
    (∃ i j, i ≠ j ∧ {s(u,v),s(x,y)} ⊆ (crossGraph G (X i) (X j)).edgeFinset) := by
  classical
  rcases paired_fibers_placement X p hux hvy with ⟨i,hu,hv,hx,hy⟩ | ⟨i,j,hij,hu,hx,hv,hy⟩
  · left
    refine ⟨i,?_⟩
    intro e he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact mem_internalGraph.mpr ⟨he,hu,hv⟩
    · exact Finset.mem_singleton.mp he' ▸ mem_internalGraph.mpr ⟨hf,hx,hy⟩
  · right
    refine ⟨i,j,hij,?_⟩
    intro e he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact mem_crossGraph.mpr ⟨he,Or.inl ⟨hu,hv⟩⟩
    · exact Finset.mem_singleton.mp he' ▸ mem_crossGraph.mpr ⟨hf,Or.inl ⟨hx,hy⟩⟩

lemma all_collisions_covered (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    CollisionPairs (Sym2.map (familyProject X hd p)) G.edgeFinset ⊆
      wedgeCover X G p ∪ internalCover X hd G p ∪ crossCover X hd G p := by
  classical
  intro q hq
  obtain ⟨hsub,hcard,himage⟩ := (mem_collisionPairs _ _ _).mp hq
  obtain ⟨e,f,hef,rfl⟩ := Finset.card_eq_two.mp hcard
  have he := hsub (by simp : e ∈ ({e,f}:Finset (Sym2 V)))
  have hf := hsub (by simp : f ∈ ({e,f}:Finset (Sym2 V)))
  have hev : edgePairEvent X hd p {e,f} := himage
  have heq := (edgePairEvent_pair X hd p e f).mp hev
  rcases distinct_edge_cases G he hf hef with hshared | hdis
  · obtain ⟨v,u,w,hvu,hvw,huw,rfl,rfl⟩ := hshared
    have hpair := shared_endpoint_collision X hd p huw heq
    obtain ⟨i,hu,hw,hpair'⟩ := hpair
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨{u,w},?_,by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_,by simp [huw]⟩,?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_filter.mpr ⟨hu,SimpleGraph.mem_edgeFinset.mp he⟩
      · exact Finset.mem_singleton.mp hz ▸ Finset.mem_filter.mpr ⟨hw,SimpleGraph.mem_edgeFinset.mp hf⟩
    · exact (vertexPairEvent_pair X p u w huw).mpr ⟨i,hu,hw,hpair'⟩
  · obtain ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl,rfl⟩ := hdis
    have hdis : DisjointEdgePair ({s(u,v),s(x,y)}:Finset (Sym2 V)) :=
      ⟨u,v,x,y,huv,hxy,hux,huy,hvx,hvy,rfl⟩
    have hplace : (∃ i, {s(u,v),s(x,y)} ⊆ (internalGraph G (X i)).edgeFinset) ∨
        (∃ i j, i ≠ j ∧ {s(u,v),s(x,y)} ⊆ (crossGraph G (X i) (X j)).edgeFinset) := by
      rcases four_endpoint_collision X hd p hux huy hvx hvy heq with hh | hh
      · exact two_paired_edges_placement X G p (SimpleGraph.mem_edgeFinset.mp he)
          (SimpleGraph.mem_edgeFinset.mp hf) hh.1 hh.2
      · have hh' := two_paired_edges_placement X G p (SimpleGraph.mem_edgeFinset.mp he)
          (SimpleGraph.mem_edgeFinset.mp hf).symm hh.1 hh.2
        simpa only [Sym2.eq_swap (a:=y) (b:=x)] using hh'
    rcases hplace with ⟨i,hi⟩ | ⟨i,j,hij,hij'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
        (mem_pairErrors X hd _ p _).mpr ⟨hi,by simp [hef],hdis,hev⟩⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨j,by simp [hij.symm],?_⟩⟩
      exact (mem_pairErrors X hd _ p _).mpr ⟨hij',by simp [hef],hdis,hev⟩

lemma all_loops_covered (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    G.edgeFinset.filter (fun e => (Sym2.map (familyProject X hd p) e).IsDiag) ⊆
      Finset.univ.biUnion (fun i => loopErrors X hd G p i) := by
  classical
  intro e he
  obtain ⟨he,hloop⟩ := Finset.mem_filter.mp he
  obtain ⟨u,v⟩ := e
  have huv := SimpleGraph.mem_edgeFinset.mp he
  obtain ⟨i,hu,hv,hp⟩ := (loop_iff_familyPaired X hd p huv.ne).mp hloop
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
    Finset.mem_filter.mpr ⟨mem_internalGraph.mpr ⟨huv,hu,hv⟩,hloop⟩⟩

lemma quotientDefect_le_budget (G : SimpleGraph V) (p : ∀ i, PairingSpace (X i)) :
    quotientDefect G (familyProject X hd p) ≤ foldErrorBudget X hd G p := by
  classical
  have hl := (Finset.card_le_card (all_loops_covered X hd G p)).trans
    (Finset.card_biUnion_le)
  have hc := (Finset.card_le_card (all_collisions_covered X hd G p)).trans
    (Finset.card_union_le _ _)
  have hw : (wedgeCover X G p).card ≤ ∑ i, ∑ v, (wedgeErrors X G p i v).card := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun v hv => Finset.card_image_le
  have hi : (internalCover X hd G p).card ≤
      ∑ i, (pairErrors X hd (internalGraph G (X i)) p).card := Finset.card_biUnion_le
  have hx : (crossCover X hd G p).card ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
      (pairErrors X hd (crossGraph G (X i) (X j)) p).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun i hi => Finset.card_biUnion_le
  have hc' := Finset.card_le_card (collisionPairs_mono (Sym2.map (familyProject X hd p))
    (Finset.filter_subset (fun e => ¬(Sym2.map (familyProject X hd p) e).IsDiag) G.edgeFinset))
  have hunion := Finset.card_union_le (wedgeCover X G p) (internalCover X hd G p)
  unfold quotientDefect foldErrorBudget
  simp only [Finset.sum_add_distrib]
  omega

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] (X : I → Finset V)
  (hd : Pairwise (fun i j => Disjoint (X i) (X j)))

lemma fold_ratio_one (m : ℝ) (hm : 8 ≤ m) : m/(m-1) ≤ 8/7 := by
  apply (div_le_iff₀ (show 0 < m-1 by linarith)).mpr
  linarith
lemma fold_ratio_three (m : ℝ) (hm : 8 ≤ m) : m/(m-3) ≤ 8/5 := by
  apply (div_le_iff₀ (show 0 < m-3 by linarith)).mpr
  linarith
lemma choose_two_real_bound (n : ℕ) : (n.choose 2 : ℝ) ≤ (n:ℝ)^2/2 := by
  rw [Nat.cast_choose_two]
  have := Nat.cast_nonneg (α:=ℝ) n
  nlinarith

lemma first_error_numeric (m a e : ℝ) (hm : 8 ≤ m) (he : 2*e ≤ a*m) :
    e/(m-1) + (a*(a-1)*m/2)/(m-1) ≤ (4/7)*a^2 := by
  have hp : 0 < m-1 := by linarith
  calc
    _ = (e+a*(a-1)*m/2)/(m-1) := by ring
    _ ≤ (a^2*m/2)/(m-1) := (div_le_div_iff_of_pos_right hp).mpr (by nlinarith)
    _ = (a^2/2)*(m/(m-1)) := by ring
    _ ≤ (a^2/2)*(8/7) := mul_le_mul_of_nonneg_left (fold_ratio_one m hm) (by positivity)
    _ = _ := by ring

lemma internal_error_numeric (m a : ℝ) (e : ℕ) (hm : 8 ≤ m) (ha : 0 ≤ a)
    (he : 2*(e:ℝ) ≤ a*m) :
    (e.choose 2 : ℝ)*(2/((m-1)*(m-3))) ≤ (16/35)*a^2 := by
  have hp : 0 < m-1 := by linarith
  have hp' : 0 < m-3 := by linarith
  have he2 : (e:ℝ)^2 ≤ (a*m/2)^2 := by
    apply sq_le_sq₀ (Nat.cast_nonneg _) (by positivity) |>.mpr
    linarith
  calc
    _ ≤ ((e:ℝ)^2/2)*(2/((m-1)*(m-3))) := mul_le_mul_of_nonneg_right
      (choose_two_real_bound e) (by positivity)
    _ = (e:ℝ)^2/((m-1)*(m-3)) := by ring
    _ ≤ (a*m/2)^2/((m-1)*(m-3)) := div_le_div_of_nonneg_right he2 (by positivity)
    _ = (a^2/4)*((m/(m-1))*(m/(m-3))) := by field_simp ; ring
    _ ≤ (a^2/4)*((8/7)*(8/5)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (fold_ratio_one m hm) (fold_ratio_three m hm)
        (by positivity) (by norm_num)) (by positivity)
    _ = _ := by ring

lemma cross_error_numeric (m n : ℝ) (e : ℕ) (hm : 8 ≤ m) (hn : 8 ≤ n) :
    (e.choose 2 : ℝ)*(1/((m-1)*(n-1))) ≤ (32/49)*((e:ℝ)^2/(m*n)) := by
  have hp : 0 < m-1 := by linarith
  have hq : 0 < n-1 := by linarith
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  calc
    _ ≤ ((e:ℝ)^2/2)*(1/((m-1)*(n-1))) := mul_le_mul_of_nonneg_right
      (choose_two_real_bound e) (by positivity)
    _ = ((e:ℝ)^2/(2*m*n))*((m/(m-1))*(n/(n-1))) := by field_simp
    _ ≤ ((e:ℝ)^2/(2*m*n))*((8/7)*(8/7)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (fold_ratio_one m hm) (fold_ratio_one n hn)
        (by positivity) (by norm_num)) (by positivity)
    _ = _ := by ring

lemma first_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 1 ≤ a)
    (hm : 8 ≤ (X i).card)
    (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((loopErrors X hd G p i).card : ℝ) + ∑ v, ((wedgeErrors X G p i v).card:ℝ)) ≤
      (4/7)*a^2 := by
  classical
  rw [finiteAverage_add,finiteAverage_sum]
  have hp : 0 < ((X i).card:ℝ)-1 := by
    have : (8:ℝ) ≤ (X i).card := by exact_mod_cast hm
    linarith
  calc
    _ ≤ ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        ∑ v, ((neighborsIn G (X i) v).choose 2 : ℝ)/((X i).card-1:ℝ) :=
      add_le_add (loopErrors_average X hd G i (by omega))
        (Finset.sum_le_sum fun v _ => wedgeErrors_average X hd G i v (by omega))
    _ = ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        (∑ v, ((neighborsIn G (X i) v).choose 2 : ℝ))/((X i).card-1:ℝ) := by rw [Finset.sum_div]
    _ ≤ ((internalGraph G (X i)).edgeFinset.card:ℝ)/((X i).card-1:ℝ) +
        (a*(a-1)*(X i).card/2)/((X i).card-1:ℝ) := by
      apply add_le_add_right
      exact div_le_div_of_nonneg_right (by exact_mod_cast wedge_count_bound G (X i) a ha hdegree hneighbor) hp.le
    _ ≤ _ := first_error_numeric _ _ _ (by exact_mod_cast hm) (internal_edge_bound G (X i) a hdegree)

lemma internal_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 0 ≤ a)
    (hm : 8 ≤ (X i).card) (hdegree : ∀ x ∈ X i, (G.degree x : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ j, PairingSpace (X j) =>
      ((pairErrors X hd (internalGraph G (X i)) p).card : ℝ)) ≤ (16/35)*a^2 :=
  (internal_pairErrors_average X hd G i (by omega)).trans
    (internal_error_numeric _ _ _ (by exact_mod_cast hm) ha (internal_edge_bound G (X i) a hdegree))

lemma cross_errors_average (G : SimpleGraph V) (i : I) (a : ℝ) (ha : 0 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ k, PairingSpace (X k) =>
      ∑ j ∈ Finset.univ.erase i, ((pairErrors X hd (crossGraph G (X i) (X j)) p).card : ℝ)) ≤
      (32/49)*a^2 := by
  classical
  rw [finiteAverage_sum]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, (32/49)*((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hij := (Finset.mem_erase.mp hj).1.symm
      exact (cross_pairErrors_average X hd G i j hij (by have := hm i; omega) (by have := hm j; omega)).trans
        (cross_error_numeric _ _ _ (by exact_mod_cast hm i) (by exact_mod_cast hm j))
    _ ≤ ∑ j, (32/49)*((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro j hj hj'
      positivity
    _ = (32/49)*∑ j, ((betweenCount G (X i) (X j):ℝ)^2 /
        ((X i).card*(X j).card)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (cross_error_row G X hd a ha (by intro i; have := hm i; omega) hdegree i) (by norm_num)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse9} {I : Type cycleUniverse10} [Fintype V] [Fintype I]

theorem folding_average_bound (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 1 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card) (hma : ∀ i, a^2 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ i v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    finiteAverage (fun p : ∀ i, PairingSpace (X i) =>
      (foldErrorBudget X hd G p : ℝ)) ≤ 2 * ∑ i, ((X i).card : ℝ) := by
  classical
  simp only [foldErrorBudget,Nat.cast_sum,Nat.cast_add]
  rw [finiteAverage_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [finiteAverage_add,finiteAverage_add]
  have hfirst := first_errors_average X hd G i a ha (hm i) (hdegree i) (hneighbor i)
  have hint := internal_errors_average X hd G i a (by linarith) (hm i) (hdegree i)
  have hcross := cross_errors_average X hd G i a (by linarith) hm hdegree
  calc
    _ ≤ (4/7)*a^2 + (16/35)*a^2 + (32/49)*a^2 :=
      add_le_add (add_le_add hfirst hint) hcross
    _ ≤ 2 * ((X i).card : ℝ) := by nlinarith [hma i,sq_nonneg a]

theorem pair_folding (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (a : ℝ) (ha : 1 ≤ a)
    (hm : ∀ i, 8 ≤ (X i).card) (hma : ∀ i, a^2 ≤ (X i).card)
    (hdegree : ∀ i x, x ∈ X i → (G.degree x : ℝ) ≤ a)
    (hneighbor : ∀ i v, (neighborsIn G (X i) v : ℝ) ≤ a) :
    ∃ (p : ∀ i, PairingSpace (X i)) (retained : Finset (Sym2 V))
      (Q : SimpleGraph (FamilyQuotient X p)),
      retained ⊆ G.edgeFinset ∧
      (G.edgeFinset \ retained).card ≤ 2 * ∑ i, (X i).card ∧
      Q.edgeSet = ((retained.image (Sym2.map (familyProject X hd p)) :
         Finset (Sym2 (FamilyQuotient X p))) : Set (Sym2 (FamilyQuotient X p))) ∧
      (∀ e ∈ Q.edgeSet, ∃! f, f ∈ retained ∧ Sym2.map (familyProject X hd p) f = e) ∧
      Fintype.card (FamilyQuotient X p) = Fintype.card V - ∑ i, (X i).card / 2 := by
  classical
  obtain ⟨p,hp⟩ := exists_le_finiteAverage (fun p : ∀ i, PairingSpace (X i) =>
      (foldErrorBudget X hd G p : ℝ))
  have hcostR := hp.trans (folding_average_bound G X hd a ha hm hma hdegree hneighbor)
  have hcost : foldErrorBudget X hd G p ≤ 2 * ∑ i, (X i).card := by exact_mod_cast hcostR
  obtain ⟨retained,Q,hsub,herr,hQ,hrep⟩ := simple_quotient_representatives G (familyProject X hd p)
  exact ⟨p,retained,Q,hsub,herr.trans ((quotientDefect_le_budget X hd G p).trans hcost),
    hQ,hrep,family_quotient_order X hd p⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V)

lemma mem_heavyNeighbors (X : Finset V) (a : ℝ) (v : V) :
    v ∈ heavyNeighbors G X a ↔ a < (neighborsIn G X v : ℝ) := by simp [heavyNeighbors]

lemma heavyNeighbors_disjoint_active (X Y : Finset V) (a : ℝ)
    (hY : ∀ v ∈ Y, (G.degree v : ℝ) ≤ a) :
    Disjoint (heavyNeighbors G X a) Y := by
  apply Finset.disjoint_left.mpr
  intro v hv hy
  have h₁ := (mem_heavyNeighbors G X a v).mp hv
  have h₂ : (neighborsIn G X v : ℝ) ≤ G.degree v := by
    exact_mod_cast neighborsIn_le_degree G X v
  exact (not_lt_of_ge (h₂.trans (hY v hy))) h₁

lemma heavyNeighbors_card_le (X : Finset V) (a : ℝ) (ha : 0 < a)
    (hX : ∀ v ∈ X, (G.degree v : ℝ) ≤ a) :
    (heavyNeighbors G X a).card ≤ X.card := by
  have hsum : a * (heavyNeighbors G X a).card ≤
      ∑ v ∈ heavyNeighbors G X a, (neighborsIn G X v : ℝ) := by
    calc
      _ = ∑ _v ∈ heavyNeighbors G X a, a := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv =>
        ((mem_heavyNeighbors G X a v).mp hv).le
  have hsub : (∑ v ∈ heavyNeighbors G X a, (neighborsIn G X v : ℝ)) ≤
      ∑ v, (neighborsIn G X v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have htotal : (∑ v, (neighborsIn G X v : ℝ)) ≤ a * X.card := by
    rw [← Nat.cast_sum, sum_incidence_to_set G X, Nat.cast_sum]
    simpa [mul_comm] using Finset.sum_le_sum (s := X) (fun v hv => hX v hv)
  have hh := hsum.trans (hsub.trans htotal)
  have := (mul_le_mul_iff_right₀ ha).mp hh
  exact_mod_cast this

variable {I : Type cycleUniverse12} [Fintype I] (X : I → Finset V)

lemma heavyDesignated_le {V : Type cycleUniverse13} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse14} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) (i : I) : heavyDesignated G X a i ≤ G :=
  fun _ _ h => h.1

theorem heavyDesignated_pairwise {V : Type cycleUniverse15} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse16} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hdegree : ∀ i v, v ∈ X i → (G.degree v : ℝ) ≤ a) :
    Pairwise (fun i j => Disjoint (heavyDesignated G X a i).edgeSet
      (heavyDesignated G X a j).edgeSet) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.ind with
  | _ u v =>
    change G.Adj u v ∧ ((u ∈ X i ∧ v ∈ heavyNeighbors G (X i) a) ∨
      (u ∈ heavyNeighbors G (X i) a ∧ v ∈ X i)) at hei
    change G.Adj u v ∧ ((u ∈ X j ∧ v ∈ heavyNeighbors G (X j) a) ∨
      (u ∈ heavyNeighbors G (X j) a ∧ v ∈ X j)) at hej
    rcases hei.2 with hi | hi <;> rcases hej.2 with hj | hj
    · exact Finset.disjoint_left.mp (hd hij) hi.1 hj.1
    · exact Finset.disjoint_left.mp
        (heavyNeighbors_disjoint_active G (X j) (X i) a (hdegree i)) hj.1 hi.1
    · exact Finset.disjoint_left.mp
        (heavyNeighbors_disjoint_active G (X i) (X j) a (hdegree j)) hi.1 hj.1
    · exact Finset.disjoint_left.mp (hd hij) hi.2 hj.2

lemma trimHeavyGraph_le {V : Type cycleUniverse17} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse18} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) : trimHeavyGraph G X a ≤ G := fun _ _ h => h.1

theorem trimHeavyGraph_neighbors {V : Type cycleUniverse19} [_contextInstance1 : Fintype V] (G : SimpleGraph V) {I : Type cycleUniverse20} [_contextInstance4 : Fintype I] (X : I → Finset V) (a : ℝ) (ha : 0 ≤ a) (i : I) (v : V) :
    (neighborsIn (trimHeavyGraph G X a) (X i) v : ℝ) ≤ a := by
  by_cases hv : v ∈ heavyNeighbors G (X i) a
  · have he : (X i).filter ((trimHeavyGraph G X a).Adj v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hui,hvu⟩ := Finset.mem_filter.mp hu
      exact hvu.2 i ⟨hvu.1,Or.inr ⟨hv,hui⟩⟩
    simpa [neighborsIn, he] using ha
  · have hnon : (neighborsIn G (X i) v : ℝ) ≤ a :=
      le_of_not_gt (fun hh => hv ((mem_heavyNeighbors G (X i) a v).mpr hh))
    apply le_trans _ hnon
    exact_mod_cast Finset.card_le_card (show
      (X i).filter ((trimHeavyGraph G X a).Adj v) ⊆ (X i).filter (G.Adj v) from
      fun u hu => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
        (Finset.mem_filter.mp hu).2.1⟩)

theorem trimHeavyGraph_degree (a : ℝ) (v : V) :
    (trimHeavyGraph G X a).degree v ≤ G.degree v := by
  classical
  exact SimpleGraph.degree_le_of_le (trimHeavyGraph_le G X a)

theorem trimHeavyGraph_ledger (a : ℝ) :
    (trimHeavyGraph G X a).edgeSet ∪
      (⋃ i, (heavyDesignated G X a i).edgeSet) = G.edgeSet ∧
    Disjoint (trimHeavyGraph G X a).edgeSet
      (⋃ i, (heavyDesignated G X a i).edgeSet) := by
  constructor
  · ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Set.mem_union, Set.mem_iUnion, SimpleGraph.mem_edgeSet]
      change (G.Adj u v ∧ ∀ i, ¬ (heavyDesignated G X a i).Adj u v) ∨
        (∃ i, (heavyDesignated G X a i).Adj u v) ↔ G.Adj u v
      constructor
      · rintro (h | ⟨i,hi⟩)
        · exact h.1
        · exact hi.1
      · intro h
        by_cases he : ∃ i, (heavyDesignated G X a i).Adj u v
        · exact Or.inr he
        · exact Or.inl ⟨h,fun i hi => he ⟨i,hi⟩⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hf
      exact he.2 i hi

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma alternating_endpoint_mem {V : Type cycleUniverse22} {G : SimpleGraph V} (X H : Set V)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) :
    (a ∈ X ∨ a ∈ H) ∧ (b ∈ X ∨ b ∈ H) := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  constructor
  · exact (hbi (p.adj_snd hn)).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · exact (hbi (p.adj_penultimate hn)).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)

lemma alternating_snd_mem {V : Type cycleUniverse23} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (ha : a ∈ H) : p.snd ∈ X := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  rcases hbi (p.adj_snd hn) with h | h
  · exact False.elim (Set.disjoint_left.mp hd h.1 ha)
  · exact h.2

lemma alternating_penultimate_mem {V : Type cycleUniverse24} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (hb : b ∈ H) :
    p.penultimate ∈ X := by
  have hn : ¬p.Nil := by intro h; have := h.length_eq_zero; omega
  rcases hbi (p.adj_penultimate hn) with h | h
  · exact h.1
  · exact False.elim (Set.disjoint_left.mp hd h.2 hb)

theorem trim_bipartite_path {V : Type cycleUniverse25} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hs : p.IsPath) (hp : 0 < p.length) :
    ∃ q : TrimmedPath G,
      q.walk.edgeSet ⊆ p.edgeSet ∧ p.length ≤ q.walk.length + 2 ∧
      (0 < q.walk.length → q.start ∈ X ∧ q.finish ∈ X) := by
  have hends := alternating_endpoint_mem X H hbi p hp
  by_cases ha : a ∈ H
  · have hsa := alternating_snd_mem X H hd hbi p hp ha
    by_cases hb : b ∈ H
    · refine ⟨⟨p.snd,p.tail.penultimate,p.tail.dropLast,hs.tail.dropLast⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_dropLast, Walk.edges_tail] at he ⊢
        exact List.mem_of_mem_tail (List.mem_of_mem_dropLast he)
      · simp only [Walk.length_dropLast,Walk.length_tail]
        omega
      · intro hpos
        have ht : 0 < p.tail.length := by
          change 0 < p.tail.dropLast.length at hpos
          rw [Walk.length_dropLast] at hpos
          omega
        exact ⟨hsa,alternating_penultimate_mem X H hd hbi p.tail ht hb⟩
    · refine ⟨⟨p.snd,b,p.tail,hs.tail⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_tail] at he ⊢
        exact List.mem_of_mem_tail he
      · simp only [Walk.length_tail]; omega
      · intro _
        exact ⟨hsa,hends.2.resolve_right hb⟩
  · by_cases hb : b ∈ H
    · refine ⟨⟨a,p.penultimate,p.dropLast,hs.dropLast⟩,?_,?_,?_⟩
      · intro e he
        simp only [Walk.mem_edgeSet, Walk.edges_dropLast] at he ⊢
        exact List.mem_of_mem_dropLast he
      · simp only [Walk.length_dropLast]; omega
      · intro _
        exact ⟨hends.1.resolve_right ha,alternating_penultimate_mem X H hd hbi p hp hb⟩
    · exact ⟨⟨a,b,p,hs⟩,Set.Subset.rfl,by change p.length ≤ p.length + 2; omega,fun _ =>
        ⟨hends.1.resolve_right ha,hends.2.resolve_right hb⟩⟩

lemma bipartite_path_length {V : Type cycleUniverse26} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hp : 0 < p.length) (ha : a ∈ X) (hb : b ∈ X) :
    2 ≤ p.length := by
  by_contra h
  have hlen : p.length = 1 := by omega
  rcases hbi (Walk.adj_of_length_eq_one hlen) with he | he
  · exact Set.disjoint_left.mp hd hb he.2
  · exact Set.disjoint_left.mp hd ha he.1

lemma path_edgeFinset_card {V : Type cycleUniverse27} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) : p.edges.toFinset.card = p.length := by
  classical
  rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]

theorem trim_bipartite_path_ledger {V : Type cycleUniverse28} {G : SimpleGraph V} (X H : Set V)
    (hd : Disjoint X H)
    (hbi : ∀ {u v}, G.Adj u v → (u ∈ X ∧ v ∈ H) ∨ (u ∈ H ∧ v ∈ X))
    {a b : V} (p : G.Walk a b) (hs : p.IsPath) (hp : 0 < p.length) :
    ∃ (q : TrimmedPath G) (discarded : Finset (Sym2 V)),
      discarded.card ≤ 2 ∧ Disjoint (discarded : Set (Sym2 V)) q.walk.edgeSet ∧
      (discarded : Set (Sym2 V)) ∪ q.walk.edgeSet = p.edgeSet ∧
      (0 < q.walk.length → q.start ∈ X ∧ q.finish ∈ X ∧ 2 ≤ q.walk.length) := by
  classical
  obtain ⟨q,hsub,hlen,hends⟩ := trim_bipartite_path X H hd hbi p hs hp
  have hfs : q.walk.edges.toFinset ⊆ p.edges.toFinset := by
    intro e he
    exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp he))
  refine ⟨q,p.edges.toFinset \ q.walk.edges.toFinset,?_,?_,?_,?_⟩
  · rw [Finset.card_sdiff_of_subset hfs, path_edgeFinset_card p hs,
      path_edgeFinset_card q.walk q.simple]
    omega
  · rw [Set.disjoint_left]
    intro e he hq
    exact (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr hq)
  · ext e
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff, List.mem_toFinset,
      Walk.mem_edgeSet]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hsub h
    · intro h
      by_cases he : e ∈ q.walk.edges
      · exact Or.inr he
      · exact Or.inl ⟨h,he⟩
  · intro hpos
    obtain ⟨ha,hb⟩ := hends hpos
    exact ⟨ha,hb,bipartite_path_length X H hd hbi q.walk hpos ha hb⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma endpoint_path_count_on {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G) (S : Finset V)
    (hends : ∀ i, (P i).start ∈ S ∧ (P i).finish ∈ S)
    (hload : ∀ v, (univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ S.card := by
  classical
  have heq : ∑ v ∈ S, (univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    have hc : ∀ i : I, (∑ v ∈ S, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : S.filter (fun v => (P i).start = v ∨ (P i).finish = v) =
          {(P i).start,(P i).finish} := by
        ext v
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
        constructor
        · intro h; simpa only [eq_comm] using h.2
        · intro h
          rcases h with rfl | rfl
          · exact ⟨(hends i).1,Or.inl rfl⟩
          · exact ⟨(hends i).2,Or.inr rfl⟩
      rw [← Finset.sum_filter,hf]
      simp [(P i).endpoints_ne]
    simp_rw [hc]
    simp [mul_comm]
  have hb := Finset.sum_le_sum (fun v (_ : v ∈ S) => hload v)
  rw [heq] at hb
  simp only [Finset.sum_const, smul_eq_mul] at hb
  omega

lemma heavy_paths {V : Type cycleUniverse32} [Fintype V] (G : SimpleGraph V)
    (X : Finset V) (a : ℝ) (ha : 0 < a)
    (hdeg : ∀ v ∈ X, (G.degree v:ℝ) ≤ a) :
    let H := heavyNeighbors G X a
    let B := crossGraph G X H
    ∃ (k : ℕ) (P : Fin k → PositiveSimplePath B),
      Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = B.edgeSet ∧ k ≤ 2 * X.card := by
  classical
  dsimp only
  obtain ⟨k,P,hd,hu,hl,_⟩ := endpoint_path_partition (crossGraph G X (heavyNeighbors G X a))
  refine ⟨k,P,hd,hu,?_⟩
  have hend : ∀ i, (P i).start ∈ X ∪ heavyNeighbors G X a ∧
      (P i).finish ∈ X ∪ heavyNeighbors G X a := by
    intro i
    have h := alternating_endpoint_mem (X:Set V) (heavyNeighbors G X a : Set V)
      (fun {_ _} (h : (crossGraph G X (heavyNeighbors G X a)).Adj _ _) => h.2) (P i).walk (P i).positive
    exact ⟨Finset.mem_union.mpr h.1,Finset.mem_union.mpr h.2⟩
  have hk := endpoint_path_count_on P (X ∪ heavyNeighbors G X a) hend hl
  rw [Fintype.card_fin] at hk
  have hh := heavyNeighbors_card_le G X a ha hdeg
  exact hk.trans ((Finset.card_union_le _ _).trans (by omega))

lemma PreparedBatch.bad_subset {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) : (b.bad : Set (Sym2 V)) ⊆ G.edgeSet := by
  rw [← b.cover]; exact Set.subset_union_of_subset_left (Set.subset_union_left) _

lemma PreparedBatch.retained_subset {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) : (b.retained : Set (Sym2 V)) ⊆ G.edgeSet := by
  rw [← b.cover]; exact Set.subset_union_of_subset_left (Set.subset_union_right) _

theorem prepare_batch {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (X : I → Finset V)
    (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (a : ℝ) (ha : 1 ≤ a) (hm : ∀ i, 8 ≤ (X i).card)
    (hma : ∀ i, a^2 ≤ (X i).card)
    (hdeg : ∀ i v, v ∈ X i → (G.degree v:ℝ) ≤ a) :
    Nonempty (PreparedBatch G X hd) := by
  classical
  let H := heavyDesignated G X a
  let T := trimHeavyGraph G X a
  have hHpair := heavyDesignated_pairwise G X a hd hdeg
  have hT := trimHeavyGraph_ledger G X a
  have hpaths : ∀ i, ∃ (k : ℕ) (P : Fin k → PositiveSimplePath (H i)),
      Pairwise (fun j l => Disjoint (P j).walk.edgeSet (P l).walk.edgeSet) ∧
      (⋃ j, (P j).walk.edgeSet) = (H i).edgeSet ∧ k ≤ 2*(X i).card :=
    fun i => heavy_paths G (X i) a (by linarith) (hdeg i)
  choose k P hPd hPu hk using hpaths
  have htrim : ∀ i j, ∃ (q : TrimmedPath (H i)) (S : Finset (Sym2 V)),
      S.card ≤ 2 ∧ Disjoint (S:Set _) q.walk.edgeSet ∧
      (S:Set _) ∪ q.walk.edgeSet = (P i j).walk.edgeSet ∧
      (0 < q.walk.length → q.start ∈ X i ∧ q.finish ∈ X i ∧ 2 ≤ q.walk.length) := by
    intro i j
    exact trim_bipartite_path_ledger (X i:Set V) (heavyNeighbors G (X i) a:Set V)
      (by simpa only [Finset.disjoint_coe] using
        (heavyNeighbors_disjoint_active G (X i) (X i) a (hdeg i)).symm)
      (fun {_ _} (h : (H i).Adj _ _) => h.2) (P i j).walk (P i j).isPath (P i j).positive
  choose q S hSnum hSq hScover hEnds using htrim
  let Qpath : ∀ i, Fin (k i) → TrimmedPath G := fun i j =>
    ⟨(q i j).start,(q i j).finish,(q i j).walk.map (SimpleGraph.Hom.ofLE (heavyDesignated_le G X a i)),
      (q i j).simple.map (Function.injective_id)⟩
  have hQedges : ∀ i j, (Qpath i j).walk.edgeSet = (q i j).walk.edgeSet := by
    intro i j; simp [Qpath,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
  have hQlen : ∀ i j, (Qpath i j).walk.length = (q i j).walk.length :=
    fun i j => Walk.length_map _ _
  have hSsub : ∀ i j, (S i j:Set _) ⊆ (P i j).walk.edgeSet := by
    intro i j; rw [← hScover i j]; exact Set.subset_union_left
  have hqsub : ∀ i j, (Qpath i j).walk.edgeSet ⊆ (P i j).walk.edgeSet := by
    intro i j; rw [hQedges,← hScover i j]; exact Set.subset_union_right
  have hPsub : ∀ i j, (P i j).walk.edgeSet ⊆ (H i).edgeSet :=
    fun i j => (P i j).walk.edges_subset_edgeSet
  have hPdall : Pairwise fun z w : Σ i, Fin (k i) =>
      Disjoint (P z.1 z.2).walk.edgeSet (P w.1 w.2).walk.edgeSet := by
    rintro ⟨i,j⟩ ⟨l,m⟩ hne
    by_cases hi : i = l
    · subst l
      exact hPd i (fun he => hne (by cases he; rfl))
    · exact (hHpair hi).mono (hPsub _ _) (hPsub _ _)
  let B := Finset.univ.biUnion fun z : Σ i, Fin (k i) => S z.1 z.2
  have hB : (B:Set (Sym2 V)) = ⋃ i, ⋃ j, (S i j : Set (Sym2 V)) := by
    ext e; simp [B]
  have hBnum : B.card ≤ 4 * ∑ i, (X i).card := by
    have hc : B.card ≤ ∑ z : Σ i, Fin (k i), (S z.1 z.2).card :=
      Finset.card_biUnion_le
    have hj : (∑ z : Σ i, Fin (k i), (S z.1 z.2).card) ≤ 2 * ∑ i, k i := by
      calc
        _ ≤ ∑ z : Σ i, Fin (k i), 2 := Finset.sum_le_sum (fun z _ => hSnum z.1 z.2)
        _ = _ := by simp [Fintype.card_sigma,mul_comm]
    have hk' := Finset.sum_le_sum (fun i (_:i∈(univ:Finset I)) => hk i)
    rw [← Finset.mul_sum] at hk'
    omega
  have hBheavy : (B:Set (Sym2 V)) ⊆ ⋃ i, (H i).edgeSet := by
    rw [hB]; exact Set.iUnion_subset (fun i => Set.iUnion_subset (fun j =>
      Set.subset_iUnion_of_subset i ((hSsub i j).trans (hPsub i j))))
  have hBhq : ∀ i j, Disjoint (B:Set (Sym2 V)) (Qpath i j).walk.edgeSet := by
    intro i j
    rw [hB,Set.disjoint_iUnion_left]
    intro l
    rw [Set.disjoint_iUnion_left]
    intro m
    by_cases he : (⟨l,m⟩ : Σ i, Fin (k i)) = ⟨i,j⟩
    · cases he
      rw [hQedges]; exact hSq i j
    · exact (hPdall he).mono (hSsub l m) (hqsub i j)
  have hdegT : ∀ i v, v ∈ X i → (T.degree v:ℝ) ≤ a := by
    intro i v hv
    exact (show (T.degree v:ℝ) ≤ G.degree v by exact_mod_cast trimHeavyGraph_degree G X a v).trans (hdeg i v hv)
  obtain ⟨p,R,Q,hR,hBad,hQ,hrep,horder⟩ := pair_folding T X hd a ha hm hma hdegT
    (trimHeavyGraph_neighbors G X a (by linarith))
  let A := T.edgeFinset \ R
  have hA : (A:Set (Sym2 V)) = T.edgeSet \ (R:Set (Sym2 V)) := by
    simp [A,SimpleGraph.coe_edgeFinset]
  have hR' : (R:Set (Sym2 V)) ⊆ T.edgeSet := by
    intro e he; exact SimpleGraph.mem_edgeFinset.mp (hR he)
  refine ⟨⟨p,Q,R,A ∪ B,k,Qpath,hk,?_,?_,?_,?_,?_,?_,?_,?_,hrep,horder⟩⟩
  · exact (Finset.card_union_le _ _).trans (by
      have hn : A.card ≤ 2 * ∑ i, (X i).card := hBad
      omega)
  · intro i j hp
    simpa only [Qpath,Walk.length_map] using hEnds i j (by rwa [hQlen] at hp)
  · intro z w hzw
    exact (hPdall hzw).mono (hqsub _ _) (hqsub _ _)
  · intro i j
    rw [Finset.coe_union,Set.disjoint_union_left]
    refine ⟨?_,hBhq i j⟩
    apply hT.2.mono
    · rw [hA]; exact Set.sdiff_subset
    · exact (hqsub i j).trans ((hPsub i j).trans (Set.subset_iUnion (fun i => (H i).edgeSet) i))
  · intro i j
    exact hT.2.mono hR' ((hqsub i j).trans ((hPsub i j).trans (Set.subset_iUnion (fun i => (H i).edgeSet) i)))
  · rw [Finset.coe_union,Set.disjoint_union_left]
    refine ⟨?_,hT.2.symm.mono hBheavy hR'⟩
    rw [hA]; exact Set.disjoint_sdiff_left
  · have hheavy : (B:Set (Sym2 V)) ∪ (⋃ i, ⋃ j, (Qpath i j).walk.edgeSet) =
        ⋃ i, (H i).edgeSet := by
      rw [hB,← Set.iUnion_union_distrib]
      congr 1
      funext i
      rw [← Set.iUnion_union_distrib]
      simp_rw [hQedges,hScover]
      exact hPu i
    rw [Finset.coe_union]
    have hAR : (A:Set (Sym2 V)) ∪ (R:Set (Sym2 V)) = T.edgeSet := by
      rw [hA]; exact Set.sdiff_union_of_subset hR'
    calc
      _ = ((A:Set _) ∪ (R:Set _)) ∪ ((B:Set _) ∪ ⋃ i, ⋃ j, (Qpath i j).walk.edgeSet) := by
        ext e; simp only [Set.mem_union]; tauto
      _ = T.edgeSet ∪ ⋃ i, (H i).edgeSet := by rw [hAR,hheavy]
      _ = G.edgeSet := hT.1
  · simpa only [Finset.coe_image] using hQ

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma family_quotient_image_order {V I : Type} [Fintype V] [Fintype I]
    (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (p : ∀ i, PairingSpace (X i)) (W : Finset V) (hX : ∀ i, X i ⊆ W) :
    (W.image (familyProject X hd p)).card + ∑ i, (X i).card / 2 = W.card := by
  classical
  let projMap := familyProject X hd p
  have hi : Set.InjOn projMap (↑Wᶜ : Set V) := by
    intro x hx y hy h
    rcases (familyProject_eq_iff X hd p x y).mp h with he | ⟨i,hx',hy',_⟩
    · exact he
    · exact False.elim (Finset.mem_compl.mp hx (hX i hx'))
  have hd' : Disjoint (W.image projMap) (Wᶜ.image projMap) := by
    apply Finset.disjoint_left.mpr
    rintro z hz hz'
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hz'
    rcases (familyProject_eq_iff X hd p y x).mp he with he | ⟨i,hy',hx',_⟩
    · subst y; exact Finset.mem_compl.mp hy hx
    · exact Finset.mem_compl.mp hy (hX i hy')
  have hu : W.image projMap ∪ Wᶜ.image projMap = univ := by
    rw [← Finset.image_union,Finset.union_compl]
    exact Finset.image_univ_of_surjective (familyProject_surjective X hd p)
  have hc := Finset.card_union_of_disjoint hd'
  rw [hu,Finset.card_univ,Finset.card_image_of_injOn hi] at hc
  have hc' := Finset.card_compl W
  have h := family_quotient_order_add X hd p
  dsimp only [projMap] at hc
  have hWcard := Finset.card_le_univ W
  omega

lemma PreparedBatch.quotient_supported {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) (W : Finset V)
    (hW : ∀ ⦃x y⦄, G.Adj x y → x ∈ W ∧ y ∈ W) :
    ∀ ⦃x y⦄, b.quotient.Adj x y →
      x ∈ W.image (familyProject X hd b.pairing) ∧
      y ∈ W.image (familyProject X hd b.pairing) := by
  classical
  intro x y hxy
  have he : s(x,y) ∈ b.quotient.edgeSet := hxy
  rw [b.quotient_edges] at he
  obtain ⟨e,he,heq⟩ := he
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := b.retained_subset he
    have hu := Finset.mem_image_of_mem (familyProject X hd b.pairing) (hW huv).1
    have hv := Finset.mem_image_of_mem (familyProject X hd b.pairing) (hW huv).2
    change s(familyProject X hd b.pairing u,familyProject X hd b.pairing v) = s(x,y) at heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hu,hv⟩
    · exact ⟨hv,hu⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

theorem routing_union_growth_step_of_boundary
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤
      h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  let E := P.interedges B Bᶜ
  let Ebad := E.filter (fun e => s(e.1, e.2) ∈ F)
  let Vbad := B.biUnion (fun v => ({v} : Finset V) ×ˢ (W v))
  let Enew := (Finset.univ : Finset V) ×ˢ (Bnext \ B)
  have hcover : E ⊆ Ebad ∪ Vbad ∪ Enew := by
    intro e he
    rcases P.mem_interedges_iff.mp he with ⟨hv, hw, hadj⟩
    have hnw : e.2 ∉ B := Finset.mem_compl.mp hw
    by_cases hdel : s(e.1, e.2) ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hdel⟩))
    by_cases hforbid : e.2 ∈ W e.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨e.1, hv, Finset.mem_product.mpr ⟨by simp, hforbid⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr
        ⟨hextend e.1 hv e.2 hnw hadj hdel hforbid, hnw⟩⟩
  have hcount : E.card ≤ Ebad.card + Vbad.card + Enew.card :=
    (Finset.card_le_card hcover).trans <|
      (Finset.card_union_le _ _).trans <|
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hforbidden : Vbad.card ≤ ∑ v ∈ B, (W v).card := by
    simpa [Vbad, Finset.card_product] using
      (Finset.card_biUnion_le (s := B) (t := fun v => ({v} : Finset V) ×ˢ W v))
  have hnew : Enew.card = Fintype.card V * (Bnext \ B).card := by
    simp [Enew]
  have hraw : E.card ≤ Ebad.card + (∑ v ∈ B, (W v).card) +
      Fintype.card V * (Bnext \ B).card := by omega
  have hsum : (∑ v ∈ B, ((W v).card : ℝ)) ≤ (h / 4) * B.card := by
    calc
      _ ≤ ∑ _v ∈ B, h / 4 := Finset.sum_le_sum hW
      _ = _ := by simp [mul_comm]
  have hcomplN : B.card + Bᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ B)
  have hcompl : (B.card : ℝ) + (Bᶜ.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcomplN
  have hlecompl : (B.card : ℝ) ≤ (Bᶜ.card : ℝ) := by linarith
  have hcut : h * (B.card : ℝ) ≤ (E.card : ℝ) := by
    simpa [min_eq_left hlecompl, E] using hexp B
  have hdiffN : (Bnext \ B).card + B.card = Bnext.card := by
    rw [Finset.card_sdiff_of_subset hmono]
    exact Nat.sub_add_cancel (Finset.card_le_card hmono)
  have hdiff : ((Bnext \ B).card : ℝ) + (B.card : ℝ) = (Bnext.card : ℝ) := by
    exact_mod_cast hdiffN
  have hrawR : (E.card : ℝ) ≤ (Ebad.card : ℝ) +
      (∑ v ∈ B, ((W v).card : ℝ)) +
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    exact_mod_cast hraw
  have hreach : h * (B.card : ℝ) / 2 ≤
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    nlinarith [hcut, hrawR, hF, hsum]
  have hdiv : h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) ≤
      ((Bnext \ B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card V : ℝ))).mpr
    nlinarith [hreach]
  calc
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ)
        = (B.card : ℝ) + h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) := by ring
    _ ≤ (B.card : ℝ) + ((Bnext \ B).card : ℝ) := add_le_add (le_refl _) hdiv
    _ = (Bnext.card : ℝ) := by linarith

lemma root_mem_walkBall (G : SimpleGraph V) (s : V) (t : ℕ) :
    s ∈ walkBall G s t := by
  exact (mem_walkBall G s s t).mpr ⟨.nil, by simp⟩

lemma walkBall_mono (G : SimpleGraph V) (s : V) {t u : ℕ} (htu : t ≤ u) :
    walkBall G s t ⊆ walkBall G s u := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_walkBall G s v t).mp hv
  exact (mem_walkBall G s v u).mpr ⟨p, hp.trans htu⟩

lemma walk_avoids_end {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s v : V} (p : (avoidGraph P F W).Walk s v) (hs : s ∉ W) : v ∉ W := by
  induction p with
  | nil => exact hs
  | cons hadj p ih => exact ih hadj.2.2.2

lemma ball_avoids (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (t : ℕ) : Disjoint (walkBall (avoidGraph P F W) s t) W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨p, _⟩ := (mem_walkBall _ _ _ _).mp hv
  exact walk_avoids_end P F W p hs

lemma walkBall_step (G : SimpleGraph V) (s v w : V) (t : ℕ)
    (hv : v ∈ walkBall G s t) (hadj : G.Adj v w) :
    w ∈ walkBall G s (t + 1) := by
  obtain ⟨p, hp⟩ := (mem_walkBall _ _ _ _).mp hv
  apply (mem_walkBall _ _ _ _).mpr
  exact ⟨p.concat hadj, by simpa using Nat.add_le_add_right hp 1⟩

lemma CutExpansion.le_order (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) :
    h ≤ (Fintype.card V : ℝ) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcomplN : 1 ≤ ({v} : Finset V)ᶜ.card := by
    simp only [Finset.card_compl, Finset.card_singleton]
    omega
  have hcompl : (1 : ℝ) ≤ (({v} : Finset V)ᶜ.card : ℝ) := by exact_mod_cast hcomplN
  have hc := hexp {v}
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hcompl, mul_one] at hc
  have hupper := P.card_interedges_le_mul ({v} : Finset V) ({v} : Finset V)ᶜ
  simp only [Finset.card_singleton, one_mul] at hupper
  have hle := (Finset.card_le_univ (({v} : Finset V)ᶜ))
  exact hc.trans (by exact_mod_cast hupper.trans hle)

lemma routingG_growth (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    r / 2 < (1 + h / (2 * r)) ^ routingG r h := by
  have hr0 : 0 < r := by linarith
  let x := h / (2 * r)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    linarith
  have hlog : h / (4 * r) ≤ Real.log (1 + h / (2 * r)) := by
    have heq : h / (4 * r) = x / 2 := by dsimp [x]; ring
    rw [heq]
    calc
      x / 2 ≤ 2 * x / (x + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxle)]
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    exact htwo
  have hlogpos : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hbase : Real.log (2 * r) ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2pos).mpr
    nlinarith
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) :=
    Nat.le_ceil _
  have hlogpow : 2 * Real.log (2 * r) ≤
      Real.log ((1 + h / (2 * r)) ^ routingG r h) := by
    rw [Real.log_pow]
    calc
      2 * Real.log (2 * r) ≤ 2 * Real.logb 2 (2 * r) := by linarith
      _ = (8 * (r / h) * Real.logb 2 (2 * r)) * (h / (4 * r)) := by
        field_simp
        ; ring
      _ ≤ (routingG r h : ℝ) * (h / (4 * r)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (routingG r h : ℝ) * Real.log (1 + h / (2 * r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsmall : Real.log (r / 2) < 2 * Real.log (2 * r) := by
    have := Real.log_le_log (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 2 * r)
    linarith
  apply (Real.log_lt_log_iff (by positivity : 0 < r / 2) (by positivity)).mp
  exact hsmall.trans_le hlogpow

lemma incidentEdges_union {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (F E : Finset (Sym2 V)) (v : V) :
    incidentEdges (F ∪ E) v = incidentEdges F v ∪ incidentEdges E v := by
  simp [incidentEdges, Finset.filter_union]

lemma incidentEdges_union_card_le (F E : Finset (Sym2 V)) (v : V) :
    (incidentEdges (F ∪ E) v).card ≤ (incidentEdges F v).card + (incidentEdges E v).card := by
  rw [incidentEdges_union]
  exact Finset.card_union_le _ _

lemma incidentEdges_sum_le (F : Finset (Sym2 V)) :
    ∑ v : V, (incidentEdges F v).card ≤ 2 * F.card := by
  have heq : ∑ v : V, (incidentEdges F v).card = ∑ e ∈ F, e.toFinset.card := by
    simp only [incidentEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp [← Sym2.mem_toFinset]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e _ => by
      rw [Sym2.card_toFinset]
      split <;> norm_num)
    _ = 2 * F.card := by simp [mul_comm]

lemma incidentEdges_path_start_le_one {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset s).card ≤ 1 := by
  have hsub : incidentEdges p.edges.toFinset s ⊆ {s(s, p.snd)} := by
    intro e he
    obtain ⟨heP, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp hs
    subst e
    have hv := hp.eq_snd_of_mem_edges (List.mem_toFinset.mp heP)
    simp [hv]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma incidentEdges_path_end_le_one (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset t).card ≤ 1 := by
  simpa using incidentEdges_path_start_le_one G p.reverse hp.reverse

lemma incidentEdges_walk_eq_empty_of_not_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t v : V}
    (p : G.Walk s t) (hv : v ∉ p.support) : incidentEdges p.edges.toFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heP, hve⟩ := Finset.mem_filter.mp he
  have hm := p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, List.mem_toFinset.mp heP, hve⟩)
  exact hv hm

lemma incidentEdges_path_le_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) (v : V) :
    (incidentEdges p.edges.toFinset v).card ≤ 2 := by
  by_cases hv : v ∈ p.support
  · have htake := incidentEdges_path_end_le_one G (p.takeUntil v hv) (hp.takeUntil hv)
    have hdrop := incidentEdges_path_start_le_one G (p.dropUntil v hv) (hp.dropUntil hv)
    have heq : p.edges.toFinset = (p.takeUntil v hv).edges.toFinset ∪ (p.dropUntil v hv).edges.toFinset := by
      have he := congrArg (fun q : G.Walk s t => q.edges.toFinset) (p.take_spec hv)
      simpa only [SimpleGraph.Walk.edges_append, List.toFinset_append] using he.symm
    rw [heq]
    exact (incidentEdges_union_card_le _ _ v).trans (by omega)
  · rw [incidentEdges_walk_eq_empty_of_not_mem G p hv]
    simp

lemma deleted_boundary_card_le_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (B : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤
      ∑ v ∈ B, (incidentEdges F v).card := by
  let T := B.biUnion (fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  have hc : ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun e : V × V => (e.1, s(e.1, e.2)))
    · intro e he
      obtain ⟨heP, heF⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨e.1, (P.mem_interedges_iff.mp heP).1, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨heF, by simp⟩
    · intro e he f hf heq
      have hsym := congrArg Prod.snd heq
      exact boundary_sym2_injective P B (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hsym
  have hT : T.card ≤ ∑ v ∈ B, (incidentEdges F v).card := by
    simpa [T] using Finset.card_biUnion_le (s := B)
      (t := fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  exact hc.trans hT

lemma walkBall_growth_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) (t : ℕ)
    (hsmall : ((walkBall (avoidGraph P F W) s t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (walkBall (avoidGraph P F W) s t).card ≤
      ((walkBall (avoidGraph P F W) s (t + 1)).card : ℝ) := by
  classical
  apply routing_union_growth_step_of_boundary P h hexp hr F _ _ (fun _ => W)
      (walkBall_mono _ s (Nat.le_succ t)) hsmall
  · calc
      _ ≤ ∑ v ∈ walkBall (avoidGraph P F W) s t, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P (walkBall (avoidGraph P F W) s t) F
      _ ≤ ∑ _v ∈ walkBall (avoidGraph P F W) s t, h / 4 := Finset.sum_le_sum (fun v _ => hF v)
      _ = _ := by simp; ring
  · exact fun _ _ => hW
  · intro v hv w _ hadj hdel hw
    have hnv := Finset.disjoint_left.mp (ball_avoids P F W s hs t) hv
    exact walkBall_step _ s v w t hv ⟨hadj, hdel, hnv, hw⟩

lemma walkBall_large_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F W) s (routingG (Fintype.card V) h)).card := by
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < Fintype.card V := by linarith
  let g := routingG (Fintype.card V) h
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  by_contra hnot
  have hend := le_of_not_gt hnot
  have hpow : ∀ j ≤ g, c ^ j ≤ (walkBall (avoidGraph P F W) s j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have H := Finset.card_pos.mpr ⟨s, root_mem_walkBall (avoidGraph P F W) s 0⟩
      have H' : 1 ≤ (walkBall (avoidGraph P F W) s 0).card := H
      simpa using (Nat.cast_le (α := ℝ)).mpr H'
    | succ j ih =>
      intro hj
      have hmono : ((walkBall (avoidGraph P F W) s j).card : ℝ) ≤
          (walkBall (avoidGraph P F W) s g).card := by
        exact_mod_cast Finset.card_le_card (walkBall_mono (avoidGraph P F W) s (by omega : j ≤ g))
      have hsmall := hmono.trans hend
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * (walkBall (avoidGraph P F W) s j).card := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ (walkBall (avoidGraph P F W) s (j + 1)).card :=
          walkBall_growth_of_incidents P h hexp hr0 F W s hs hF hW j hsmall
  have hg := routingG_growth (Fintype.card V) h (by linarith) hh (hexp.le_order P h hr)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma exists_short_avoiding_path (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : (avoidGraph P F W).Walk s t, q.IsPath ∧
      q.length ≤ 2 * routingG (Fintype.card V) h := by
  classical
  let g := routingG (Fintype.card V) h
  let B₁ := walkBall (avoidGraph P F W) s g
  let B₂ := walkBall (avoidGraph P F W) t g
  have h₁ := walkBall_large_of_incidents P h hh hexp hr F W s hs hF hW
  have h₂ := walkBall_large_of_incidents P h hh hexp hr F W t ht hF hW
  have hmeet : (B₁ ∩ B₂).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_union_add_card_inter B₁ B₂
    have hu := Finset.card_le_univ (B₁ ∪ B₂)
    have hsum : (Fintype.card V : ℝ) < (B₁.card : ℝ) + (B₂.card : ℝ) := by
      dsimp [B₁, B₂, g]; linarith
    have hsumN : Fintype.card V < B₁.card + B₂.card := by exact_mod_cast hsum
    omega
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨p₁, hp₁⟩ := (mem_walkBall _ s v g).mp (Finset.mem_inter.mp hv).1
  obtain ⟨p₂, hp₂⟩ := (mem_walkBall _ t v g).mp (Finset.mem_inter.mp hv).2
  let w := p₁.append p₂.reverse
  refine ⟨w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans ?_⟩
  dsimp [w]
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

lemma two_routingG_le_length (r h : ℝ) : 2 * routingG r h ≤ routingLength r h := by
  dsimp [routingLength]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma routingLength_bounds (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) :
    1 ≤ routingLength r h ∧ r ≤ (routingLength r h : ℝ) * h := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * r)
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) := Nat.le_ceil _
  have hgh : 8 * r ≤ (routingG r h : ℝ) * h := by
    calc
      8 * r = (8 * (r / h)) * h := by field_simp
      _ ≤ (8 * (r / h) * Real.logb 2 (2 * r)) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (r / h) by positivity)
      _ ≤ (routingG r h : ℝ) * h := mul_le_mul_of_nonneg_right hg hh.le
  have hgpos : 0 < routingG r h := by
    have hgR : (0 : ℝ) < routingG r h := by nlinarith
    exact_mod_cast hgR
  have hgle : routingG r h ≤ routingLength r h := (by omega : routingG r h ≤ 2 * routingG r h).trans (two_routingG_le_length r h)
  refine ⟨by omega, ?_⟩
  have hgleR : (routingG r h : ℝ) ≤ routingLength r h := by exact_mod_cast hgle
  nlinarith

lemma routing_budget (L k b z h r : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hz : 0 ≤ z) (hh : 0 < h) (_hr : 0 ≤ r)
    (hreach : r ≤ L * h) (hbudget : 64 * (L ^ 2 * (k + b) + z) ≤ h) :
    h / 8 + 2 + k ≤ h / 4 ∧ z + b * L ≤ h / 8 ∧ 64 * L * k * r ≤ h ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLLs : L ≤ L ^ 2 := by nlinarith
  have hbig : 64 * (k + b) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : 0 ≤ k + b)]
      _ ≤ _ := hbudget
  have hbL : 64 * (b * L + z) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_left hLLs hb0, mul_nonneg (sq_nonneg L) hk0]
      _ ≤ _ := hbudget
  have hkL : 64 * L ^ 2 * k ≤ h := by nlinarith [mul_nonneg (sq_nonneg L) hb0]
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    64 * L * k * r ≤ 64 * L * k * (L * h) := mul_le_mul_of_nonneg_left hreach (by positivity)
    _ = (64 * L ^ 2 * k) * h := by ring
    _ ≤ h * h := mul_le_mul_of_nonneg_right hkL hh.le
    _ = h ^ 2 := by ring

lemma saturated_card_le (F : Finset (Sym2 V)) (h : ℝ) (hh : 0 < h)
    (hF : 128 * (F.card : ℝ) ≤ h ^ 2) : (saturated F h).card ≤ h / 8 := by
  classical
  have hs : h / 8 * (saturated F h).card ≤ ∑ v : V, ((incidentEdges F v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ saturated F h, h / 8 := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F h, ((incidentEdges F v).card : ℝ) := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsum : (∑ v : V, ((incidentEdges F v).card : ℝ)) ≤ 2 * (F.card : ℝ) := by
    exact_mod_cast incidentEdges_sum_le F
  nlinarith

lemma pathInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : SimpleGraph V} {s t : V} (q : P.Walk s t) :
    (pathInterior q).card ≤ q.length := by
  have hp := List.toFinset_card_le q.support
  rw [q.length_support] at hp
  have hstart : s ∈ q.support.toFinset ∩ ({s, t} : Finset V) := by simp
  have hint := Finset.card_pos.mpr ⟨s, hstart⟩
  have hd := Finset.card_sdiff_add_card_inter q.support.toFinset ({s, t} : Finset V)
  dsimp [pathInterior]
  omega

lemma avoidGraph_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    avoidGraph P F W ≤ P := fun _ _ h => h.1

lemma walk_avoids_support (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) (hs : s ∉ W) :
    Disjoint q.support.toFinset W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  exact walk_avoids_end P F W (q.takeUntil v (List.mem_toFinset.mp hv)) hs

lemma walk_avoids_edges {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) :
    Disjoint q.edges.toFinset F := by
  apply Finset.disjoint_left.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w => exact (q.adj_of_mem_edges (List.mem_toFinset.mp he)).2.1

lemma exists_short_path_with_avoidance (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ routingLength (Fintype.card V) h ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  obtain ⟨q, hp, hl⟩ := exists_short_avoiding_path P h hh hexp hr F W s t hs ht hF hW
  refine ⟨q.mapLe (avoidGraph_le P F W), hp.mapLe _, ?_, ?_, ?_⟩
  · simpa using hl.trans (two_routingG_le_length (Fintype.card V) h)
  · simpa using walk_avoids_edges P F W q
  · simpa using walk_avoids_support P F W q hs

lemma route_degree_update {P : SimpleGraph V} {s t : V} (q : P.Walk s t)
    (hp : q.IsPath) (F : Finset (Sym2 V)) (h : ℝ) (load : V → ℕ)
    (hdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 8 + 2 + load v)
    (havoid : Disjoint q.support.toFinset (saturated F h \ {s, t})) (v : V) :
    ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      h / 8 + 2 + load v + (if v = s ∨ v = t then 1 else 0) := by
  classical
  have hadd : ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      (incidentEdges F v).card + (incidentEdges q.edges.toFinset v).card := by
    exact_mod_cast incidentEdges_union_card_le F q.edges.toFinset v
  by_cases hv : v = s ∨ v = t
  · rw [ite_eq_left hv]
    have hqN : (incidentEdges q.edges.toFinset v).card ≤ 1 := by
      rcases hv with rfl | rfl
      · exact incidentEdges_path_start_le_one P q hp
      · exact incidentEdges_path_end_le_one P q hp
    have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 1 := by exact_mod_cast hqN
    linarith [hdegree v]
  · rw [ite_eq_right hv]
    by_cases hmem : v ∈ q.support
    · have hns : v ∉ saturated F h := by
        intro hsat
        apply Finset.disjoint_left.mp havoid (List.mem_toFinset.mpr hmem)
        exact Finset.mem_sdiff.mpr ⟨hsat, by simpa using hv⟩
      have hsmall : ((incidentEdges F v).card : ℝ) < h / 8 := by
        simpa [saturated] using hns
      have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 2 := by
        exact_mod_cast incidentEdges_path_le_two P q hp v
      have : (0 : ℝ) ≤ load v := by positivity
      linarith
    · rw [incidentEdges_walk_eq_empty_of_not_mem P q hmem] at hadd
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hadd
      linarith [hdegree v]

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

lemma endpointLoad_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {A B : Finset I} (hAB : A ⊆ B) (x y : I → V) (v : V) :
    endpointLoad A x y v ≤ endpointLoad B x y v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

lemma endpointLoad_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (i : I) (hi : i ∉ A) (x y : I → V) (v : V) :
    endpointLoad (insert i A) x y v = endpointLoad A x y v +
      (if v = x i ∨ v = y i then 1 else 0) := by
  classical
  by_cases hv : v = x i ∨ v = y i
  · have hv' : x i = v ∨ y i = v := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv', hi]
  · have hv' : ¬ (x i = v ∨ y i = v) := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv']

lemma endpointLoad_sum {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (x y : I → V) (hxy : ∀ i ∈ A, x i ≠ y i) :
    ∑ v : V, endpointLoad A x y v = 2 * A.card := by
  classical
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have heq : ∀ i ∈ A, (∑ v : V, if x i = v ∨ y i = v then 1 else 0) = 2 := by
    intro i hi
    have hf : (Finset.univ.filter fun v => x i = v ∨ y i = v) = ({x i, y i} : Finset V) := by
      ext v
      simp [eq_comm]
    have hc : ({x i, y i} : Finset V).card = 2 := by simp [hxy i hi]
    rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ _i ∈ A, 2 := Finset.sum_congr rfl heq
    _ = _ := by simp [mul_comm]

lemma usedEdges_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) (L : ℕ)
    (hq : ∀ i ∈ A, (q i).length ≤ L) : (usedEdges A q).card ≤ L * A.card := by
  calc
    _ ≤ ∑ i ∈ A, (q i).edges.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, L := Finset.sum_le_sum (fun i hi => by
      have hc := List.toFinset_card_le (q i).edges
      simpa using hc.trans (by simpa using hq i hi))
    _ = _ := by simp [mul_comm]

lemma usedEdges_update_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (i : I) (hi : i ∉ A)
    (q : ∀ j, P.Walk (x j) (y j)) (p : P.Walk (x i) (y i)) :
    usedEdges (insert i A) (Function.update q i p) = usedEdges A q ∪ p.edges.toFinset := by
  classical
  rw [usedEdges, Finset.biUnion_insert]
  simp only [Function.update_self]
  rw [Finset.union_comm]
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

lemma teamInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} {T : Type} [_contextInstance5 : Fintype I] [_contextInstance6 : DecidableEq I] [_contextInstance7 : DecidableEq T] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) (L : ℕ) (b : ℝ)
    (hq : ∀ j ∈ A, (q j).length ≤ L)
    (hb : ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b) :
    ((teamInterior A q team i).card : ℝ) ≤ b * L := by
  have hc : (teamInterior A q team i).card ≤ L * (A.filter (fun j => team j = team i)).card := by
    calc
      _ ≤ ∑ j ∈ A.filter (fun j => team j = team i), (pathInterior (q j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A.filter (fun j => team j = team i), L := Finset.sum_le_sum (fun j hj =>
        (pathInterior_card_le (q j)).trans (hq j (Finset.mem_filter.mp hj).1))
      _ = _ := by simp [mul_comm]
  have hcard : ((A.filter (fun j => team j = team i)).card : ℝ) ≤ b := by
    apply le_trans _ hb
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
  have hcR : ((teamInterior A q team i).card : ℝ) ≤ (L : ℝ) * (A.filter (fun j => team j = team i)).card := by exact_mod_cast hc
  calc
    _ ≤ (L : ℝ) * b := hcR.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = _ := mul_comm _ _

theorem routing (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ) ^ 2 * (k + b) + z) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let L := routingLength (Fintype.card V) h
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  obtain ⟨hL, hreach⟩ := routingLength_bounds (Fintype.card V) h (by linarith) hh
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hdegBudget, hforbidBudget, hnumBudget⟩ := routing_budget L k b z h (Fintype.card V)
    hLR hk hb hz hh (by positivity) hreach hbudget
  have hloadA : ∀ (A : Finset I) v, (endpointLoad A x y v : ℝ) ≤ k := by
    intro A v
    have hm : (endpointLoad A x y v : ℝ) ≤ endpointLoad Finset.univ x y v := by
      exact_mod_cast endpointLoad_mono (Finset.subset_univ A) x y v
    exact hm.trans (hload v)
  have htotal : 2 * (Fintype.card I : ℝ) ≤ k * Fintype.card V := by
    have heq := endpointLoad_sum Finset.univ x y (fun i _ => hxy i)
    have heqR : (∑ v : V, (endpointLoad Finset.univ x y v : ℝ)) = 2 * Fintype.card I := by
      exact_mod_cast heq
    rw [← heqR]
    calc
      _ ≤ ∑ _v : V, k := Finset.sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [mul_comm]
  have hdefault : ∀ i, ∃ p : P.Walk (x i) (y i), p.IsPath := by
    intro i
    obtain ⟨p, hp, _⟩ := exists_short_path_with_avoidance P h hh hexp hr ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨p, hp⟩
  choose defaultPath hdefaultPath using hdefault
  have hpartial : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i), PartialRoutes P x y team Z L h A q := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultPath, ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [usedEdges, Finset.biUnion_empty, incidentEdges, Finset.filter_empty,
          Finset.card_empty, Nat.cast_zero, endpointLoad, add_zero]
        linarith
    | @insert i A hi ih =>
      obtain ⟨q, hq⟩ := ih
      let F := usedEdges A q
      let S := saturated F h
      let B := teamInterior A q team i
      let W := (S ∪ Z i ∪ B) \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hc : (F.card : ℝ) ≤ (L : ℝ) * A.card := by
          exact_mod_cast usedEdges_card_le A q L hq.short
        have ha : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ A
        have hsize : 2 * (A.card : ℝ) ≤ k * Fintype.card V := by linarith
        have hmult := mul_le_mul_of_nonneg_left hsize (show 0 ≤ (L : ℝ) by positivity)
        nlinarith [hnumBudget]
      have hS : (S.card : ℝ) ≤ h / 8 := saturated_card_le F h hh hFcard
      have hB : (B.card : ℝ) ≤ b * L := teamInterior_card_le A q team i L b hq.short (hteam i)
      have hW : (W.card : ℝ) ≤ h / 4 := by
        have hc : W.card ≤ S.card + (Z i).card + B.card :=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        have hcR : (W.card : ℝ) ≤ (S.card : ℝ) + (Z i).card + B.card := by exact_mod_cast hc
        linarith [hZ i]
      have hFdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        intro v
        have hd := hq.degree v
        have hl := hloadA A v
        dsimp [F]
        linarith
      obtain ⟨p, hp, hpL, hpF, hpW⟩ := exists_short_path_with_avoidance P h hh hexp hr F W (x i) (y i)
        (by simp [W]) (by simp [W]) hFdegree hW
      have hpZ : Disjoint (pathInterior p) (Z i) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvZ
        obtain ⟨hvp, hvends⟩ := Finset.mem_sdiff.mp hv
        apply Finset.disjoint_left.mp hpW hvp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hvZ), hvends⟩
      have hpS : Disjoint p.support.toFinset (saturated F h \ {x i, y i}) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvS
        obtain ⟨hs, he⟩ := Finset.mem_sdiff.mp hvS
        apply Finset.disjoint_left.mp hpW hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hs), he⟩
      have hpEdge : ∀ j ∈ A, Disjoint p.edges.toFinset (q j).edges.toFinset := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro e hep heq
        exact Finset.disjoint_left.mp hpF hep (Finset.mem_biUnion.mpr ⟨j, hj, heq⟩)
      have hpTeam : ∀ j ∈ A, team i = team j → Disjoint (pathInterior p) (pathInterior (q j)) := by
        intro j hj htm
        apply Finset.disjoint_left.mpr
        intro v hvp hvq
        obtain ⟨hvp', hvends⟩ := Finset.mem_sdiff.mp hvp
        apply Finset.disjoint_left.mp hpW hvp'
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ ?_, hvends⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, htm.symm⟩, hvq⟩
      let q' := Function.update q i p
      have hsame : q' i = p := Function.update_self i p q
      have hother : ∀ j ∈ A, q' j = q j := by
        intro j hj
        apply Function.update_of_ne
        intro hji
        exact hi (hji ▸ hj)
      refine ⟨q', ?_⟩
      constructor
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hp
        · simpa only [hother j hj] using hq.simple j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpL
        · simpa only [hother j hj] using hq.short j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpZ
        · simpa only [hother j hj] using hq.avoids j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpEdge k hkA
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpEdge j hjA).symm
          · simpa only [hother j hjA, hother k hkA] using hq.edge_disjoint j hjA k hkA hjk
      · intro j hj k hk hjk htm
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpTeam k hkA htm
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpTeam j hjA htm.symm).symm
          · simpa only [hother j hjA, hother k hkA] using hq.team_disjoint j hjA k hkA hjk htm
      · intro v
        have heq : usedEdges (insert i A) q' = F ∪ p.edges.toFinset := usedEdges_update_insert A i hi q p
        rw [heq]
        have hu := route_degree_update p hp F h (endpointLoad A x y) hq.degree hpS v
        have hloadEq : (endpointLoad (insert i A) x y v : ℝ) =
            endpointLoad A x y v + (if v = x i ∨ v = y i then (1 : ℝ) else 0) := by
          rw [endpointLoad_insert A i hi]
          split_ifs <;> simp
        rw [hloadEq]
        simpa only [add_assoc] using hu
  obtain ⟨q, hq⟩ := hpartial Finset.univ
  exact ⟨q, fun i => ⟨hq.simple i (by simp), hq.short i (by simp), hq.avoids i (by simp)⟩,
    fun i j hij => hq.edge_disjoint i (by simp) j (by simp) hij,
    fun i j hij htm => hq.team_disjoint i (by simp) j (by simp) hij htm⟩

end Families
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CycleLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Real Filter Asymptotics

lemma routing_length_upper (r h : ℝ) (hr : 2 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    (routingLength r h : ℝ) ≤ 108*(r/h)*(logb 2 r)^2 := by
  have hr0 : 0 < r := by linarith
  have hl : 1 ≤ logb 2 r := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 2) hr
  have hR : 1 ≤ r/h := (le_div_iff₀ hh).mpr (by simpa using hhr)
  have hlog : logb 2 (2*r) = 1 + logb 2 r := by
    rw [Real.logb_mul (by norm_num) hr0.ne']
    norm_num
  have hg := Nat.ceil_lt_add_one (show 0 ≤ 8*(r/h)*logb 2 (2*r) by rw [hlog]; positivity)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ logb 2 r by linarith)
  change (routingG r h : ℝ) < 8*(r/h)*logb 2 (2*r)+1 at hg
  change (routingDepth r : ℝ) < logb 2 r + 1 at hd
  rw [hlog] at hg
  have hprod : 1 ≤ (r/h)*logb 2 r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
  have hg' : (routingG r h : ℝ) ≤ 18*(r/h)*logb 2 r := by nlinarith
  have hd' : (1 + routingDepth r : ℝ) ≤ 3*logb 2 r := by linarith
  have hm := mul_le_mul hg' hd' (by positivity) (by positivity)
  dsimp [routingLength]
  push_cast
  nlinarith

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

theorem eventually_routing_length (c β γ δ : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 2 ≤ r → r ≤ D^β → c*D^γ ≤ r →
      (routingLength r (c*D^γ) : ℝ) ≤ D^(β-γ+δ) := by
  filter_upwards [eventually_logb_le_power (δ/4) (by positivity),
    eventually_constant_le_power (108*β^2/c) (δ/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with D hlog hconst hD r hr hrD hhr
  have hD0 : 0 < D := by linarith
  have hpowγ : 0 < D^γ := Real.rpow_pos_of_pos hD0 _
  have hden : 0 < c*D^γ := mul_pos hc hpowγ
  have hlog0 : 0 ≤ logb 2 r := (Real.logb_pos (by norm_num) (by linarith)).le
  have hlogR : logb 2 r ≤ β*D^(δ/4) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by linarith : 0 < r) hrD
    rw [Real.logb_rpow_eq_mul_logb_of_pos hD0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog hβ.le)
  have hratio : r/(c*D^γ) ≤ D^(β-γ)/c := by
    calc
      _ ≤ D^β/(c*D^γ) := div_le_div_of_nonneg_right hrD hden.le
      _ = _ := by rw [Real.rpow_sub hD0]; ring
  have hsq : (logb 2 r)^2 ≤ β^2*D^(δ/2) := by
    calc
      _ ≤ (β*D^(δ/4))^2 := pow_le_pow_left₀ hlog0 hlogR 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]; congr 2; ring
  calc
    (routingLength r (c*D^γ) : ℝ) ≤ 108*(r/(c*D^γ))*(logb 2 r)^2 :=
      routing_length_upper r (c*D^γ) hr hden hhr
    _ ≤ 108*(D^(β-γ)/c)*(β^2*D^(δ/2)) := by gcongr
    _ = (108*β^2/c)*D^(β-γ+δ/2) := by rw [Real.rpow_add hD0]; ring
    _ ≤ D^(δ/2)*D^(β-γ+δ/2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hD0.le _)
    _ = D^(β-γ+δ) := by rw [← Real.rpow_add hD0]; congr 1; ring

theorem batch_routing_margin : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
    2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
      (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
      2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
    filter_upwards [eventually_routing_length (1/4) (51/50) (9/10) (2/25)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_const_mul_power_le 1024 (7/10) (9/10) (by norm_num),
      eventually_constant_le_power 2 (9/10) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcost htwo hD r hr hrD
    have hD0 : 0 < D := by linarith
    have hr2 : 2 ≤ r := htwo.trans hr
    have hh : (1/4)*D^(9/10:ℝ) ≤ r := by
      have hh0 := Real.rpow_nonneg hD0.le (9/10:ℝ)
      linarith
    have hL := hlen r hr2 hrD hh
    norm_num at hL
    have hL' : (routingLength r (D^(9/10:ℝ)/4) : ℝ) ≤ D^(1/5:ℝ) := by
      convert hL using 1 ; ring_nf
    have hsmall : D^(1/100:ℝ) ≤ D^(3/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have h37 : D^(3/10:ℝ) ≤ D^(7/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have hprod : (routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ)) ≤ 2*D^(7/10:ℝ) := by
      calc
        _ ≤ (D^(1/5:ℝ))^2 * (2*D^(3/10:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    refine ⟨hr2, ?_⟩
    nlinarith only [hprod, h37, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

lemma subtype_image_compl {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W : Finset V) (U : Finset (W : Set V)) :
    Uᶜ.image Subtype.val = W \ U.image Subtype.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx (Subtype.ext he ▸ hy)
  · rintro ⟨hv,hvU⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro hx
    exact hvU ⟨⟨v,hv⟩,hx,rfl⟩

lemma induced_interedges_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (U : Finset (W : Set V)) :
    (((P.induce (W : Set V)).interedges U Uᶜ).card : ℝ) =
      ((P.interedges (U.image Subtype.val) (W \ U.image Subtype.val)).card : ℝ) := by
  classical
  let f : ↥(W : Set V) × ↥(W : Set V) → V × V := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have heq : ((P.induce (W : Set V)).interedges U Uᶜ).image f =
      P.interedges (U.image Subtype.val) (W \ U.image Subtype.val) := by
    rw [← subtype_image_compl W U]
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩
      exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
    · rintro ⟨⟨x,hx,hxe⟩,⟨y,hy,hye⟩,he⟩
      refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext hxe hye⟩
      change P.Adj x.val y.val
      simpa only [hxe,hye] using he
  rw [← heq, Finset.card_image_of_injective _ hf]

lemma cutExpansion_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (hexp : CutExpansionOn P W h) :
    CutExpansion (P.induce (W : Set V)) h := by
  classical
  intro U
  have hsub : U.image Subtype.val ⊆ W := by
    rintro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have h := hexp (U.image Subtype.val) hsub
  have he : W \ U.image Subtype.val = Uᶜ.image Subtype.val :=
    (subtype_image_compl W U).symm
  rw [he] at h
  simp only [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [induced_interedges_card,he]
  exact h

lemma pathInterior_map {A B : Type} [DecidableEq A] [DecidableEq B]
    {H : SimpleGraph A} {J : SimpleGraph B} (f : H →g J)
    (hf : Function.Injective f) {a b : A} (p : H.Walk a b) :
    pathInterior (p.map f) = (pathInterior p).image f := by
  classical
  simp only [pathInterior, SimpleGraph.Walk.support_map]
  rw [Finset.image_sdiff _ _ hf]
  have hm : (p.support.map f).toFinset = p.support.toFinset.image f := by
    ext v; simp
  rw [hm]
  simp

theorem team_routing_on_set {I T : Type} [Fintype I]
    (G P : SimpleGraph V) [DecidableRel P.Adj] (hPG : P ≤ G)
    (W : Finset V) (h : ℝ) (hh : 0 < h)
    (hexp : CutExpansionOn P W h) (hr : 2 ≤ W.card)
    (x y : I → V) (hx : ∀ i, x i ∈ W) (hy : ∀ i, y i ∈ W)
    (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength W.card h : ℝ)^2 * (k+b) + z) ≤ h) :
    ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card h ∧
        (∀ v ∈ (q i).support, v ∈ W) ∧ (q i).edgeSet ⊆ P.edgeSet ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      (∀ i j, i ≠ j → team i = team j →
        Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let X : I → (W : Set V) := fun i => ⟨x i,hx i⟩
  let Y : I → (W : Set V) := fun i => ⟨y i,hy i⟩
  let Z' : I → Finset (W : Set V) := fun i => univ.filter (fun v => v.val ∈ Z i)
  have hl (v : (W : Set V)) : (endpointLoad univ X Y v : ℝ) ≤ k := by
    simpa only [endpointLoad,X,Y,Subtype.ext_iff] using hload v.val
  have hz' : ∀ i, ((Z' i).card : ℝ) ≤ z := by
    intro i
    apply le_trans _ (hZ i)
    have hc : (Z' i).card ≤ (Z i).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro v hv; exact (Finset.mem_filter.mp hv).2
      · exact Subtype.val_injective.injOn
    exact_mod_cast hc
  obtain ⟨q,hq,hd,ht⟩ := routing (P.induce (W : Set V)) h hh
    (cutExpansion_induce P W h hexp) (by simpa using hr) X Y
    (fun i he => hxy i (congrArg Subtype.val he)) team Z' k b z hk hb hz hl hteam hz'
    (by simpa using hbudget)
  let f : (P.induce (W : Set V)) →g G :=
    { toFun := Subtype.val, map_rel' := fun ha => hPG ha }
  have hf : Function.Injective f := Subtype.val_injective
  have hcard : Fintype.card ↥(W : Set V) = W.card := Fintype.card_coe W
  let Q : ∀ i, G.Walk (x i) (y i) := fun i => (q i).map f
  refine ⟨Q,?_,?_,?_⟩
  · intro i
    refine ⟨(hq i).1.map hf,?_,?_,?_,?_⟩
    · simpa only [Q,SimpleGraph.Walk.length_map,hcard] using (hq i).2.1
    · intro v hv
      have hv' : v ∈ (q i).support.map f := by simpa only [Q,SimpleGraph.Walk.support_map] using hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv'
      exact a.property
    · intro e he
      rw [SimpleGraph.Walk.edgeSet_map] at he
      obtain ⟨d,hd,rfl⟩ := he
      induction d using Sym2.ind with
      | _ a b => exact (q i).adj_of_mem_edges hd
    · rw [show Q i = (q i).map f from rfl, pathInterior_map f hf]
      apply Finset.disjoint_left.mpr
      intro v hv hzv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.disjoint_left.mp (hq i).2.2 ha (by simpa [Z',f] using hzv)
  · intro i j hij
    change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet
    rw [SimpleGraph.Walk.edgeSet_map,SimpleGraph.Walk.edgeSet_map,
      Set.disjoint_image_iff (Sym2.map.injective hf)]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (hd i j hij) (by simpa using he) (by simpa using he')
  · intro i j hij hteam'
    change Disjoint (pathInterior ((q i).map f)) (pathInterior ((q j).map f))
    rw [pathInterior_map f hf,pathInterior_map f hf,Finset.disjoint_image hf]
    exact ht i j hij hteam'

theorem uniform_batch_routing :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A],
      ∀ (G P : SimpleGraph A) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset A, CutExpansionOn P W (D^(9/10:ℝ)/4) →
      D^(9/10:ℝ) ≤ (W.card : ℝ) → (W.card : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I T : Type) [Fintype I] (x y : I → A),
      (∀ i, x i ∈ W) → (∀ i, y i ∈ W) → (∀ i, x i ≠ y i) →
      ∀ (team : I → T) (Z : I → Finset A),
      (∀ v, (endpointLoad univ x y v : ℝ) ≤ D^(1/100:ℝ)) →
      (∀ i, ((univ.filter (fun j => team j = team i)).card : ℝ) ≤ D^(3/10:ℝ)) →
      (∀ i, ((Z i).card : ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(9/10:ℝ)/4) ∧
          (∀ v ∈ (q i).support, v ∈ W) ∧ (q i).edgeSet ⊆ P.edgeSet ∧
          Disjoint (pathInterior (q i)) (Z i)) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i j, i ≠ j → team i = team j →
          Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  obtain ⟨D₀,hD₀,hm⟩ := batch_routing_margin
  refine ⟨D₀,hD₀,?_⟩
  intro D hD A _ _ G P _ hPG W hexp hr₁ hr₂ I T _ x y hx hy hxy team Z hl ht hZ
  have hD1 : 1 < D := hD₀.trans_le hD
  have hD0 : 0 < D := lt_trans zero_lt_one hD1
  obtain ⟨hr,hbudget⟩ := hm D hD W.card hr₁ hr₂
  apply team_routing_on_set G P hPG W _ (by positivity) hexp (by exact_mod_cast hr)
    x y hx hy hxy team Z _ _ _ _ _ (by positivity) hl ht hZ hbudget
  · exact Real.one_le_rpow hD1.le (by norm_num)
  · exact Real.one_le_rpow hD1.le (by norm_num)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open SimpleGraph

variable {V : Type cycleUniverse1} {G : SimpleGraph V}

noncomputable section
attribute [local instance] Classical.propDecidable

theorem orient_edge_representatives {W : Type cycleUniverse4} {Q : SimpleGraph W}
    (projMap : V → W) (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃ f ∈ S, Sym2.map projMap f = e) :
    ∃ R : Q.Dart → G.Dart, ∀ d,
      (R d).edge ∈ S ∧ projMap (R d).fst = d.fst ∧ projMap (R d).snd = d.snd := by
  have hex : ∀ d : Q.Dart, ∃ r : G.Dart,
      r.edge ∈ S ∧ projMap r.fst = d.fst ∧ projMap r.snd = d.snd := by
    intro d
    obtain ⟨f,hf,hmap⟩ := hrep d.edge d.edge_mem
    induction f using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := hSG hf
      change s(projMap x,projMap y) = s(d.fst,d.snd) at hmap
      rcases Sym2.eq_iff.mp hmap with he | he
      · exact ⟨⟨(x,y),hadj⟩,hf,he.1,he.2⟩
      · refine ⟨⟨(y,x),hadj.symm⟩,?_,he.2,he.1⟩
        change s(y,x) ∈ S
        simpa only [Sym2.eq_swap] using hf
  exact Classical.axiomOfChoice hex

lemma portFrom_on {A : Type cycleUniverse7} {W : Type cycleUniverse8} (L : List A) (f : A → W) (g : A → V)
    (v₀ : V) (hn : (L.map f).Nodup) {d : A} (hd : d ∈ L) :
    portFrom L f g v₀ (f d) = g d := by
  have hex : ∃ e ∈ L, f e = f d := ⟨d,hd,rfl⟩
  rw [portFrom, dite_eq_left hex]
  congr 1
  exact List.inj_on_of_nodup_map hn hex.choose_spec.1 hd hex.choose_spec.2

theorem choose_cycle_ports {W : Type cycleUniverse9} {Q : SimpleGraph W}
    (projMap : V → W) (R : Q.Dart → G.Dart)
    (hprojMap : ∀ d, projMap (R d).fst = d.fst ∧ projMap (R d).snd = d.snd)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle) (v₀ : V) :
    ∃ s t : W → V,
      (∀ d ∈ p.darts, t d.fst = (R d).fst ∧ s d.snd = (R d).snd) ∧
      (∀ z ∈ p.dropLast.support, projMap (s z) = z ∧ projMap (t z) = z) := by
  let s := portFrom p.darts (fun d => d.snd) (fun d => (R d).snd) v₀
  let t := portFrom p.darts (fun d => d.fst) (fun d => (R d).fst) v₀
  have hnf : (p.darts.map (fun d => d.fst)).Nodup := by
    rw [Walk.map_fst_darts]
    exact hp.nodup_dropLast_support
  have hns : (p.darts.map (fun d => d.snd)).Nodup := by
    rw [Walk.map_snd_darts]
    exact hp.support_nodup
  have ht : ∀ d ∈ p.darts, t d.fst = (R d).fst := fun d hd =>
    portFrom_on _ _ _ _ hnf hd
  have hs : ∀ d ∈ p.darts, s d.snd = (R d).snd := fun d hd =>
    portFrom_on _ _ _ _ hns hd
  refine ⟨s,t,fun d hd => ⟨ht d hd,hs d hd⟩,?_⟩
  intro z hz
  have hz' : z ∈ p.support.dropLast := by
    rw [← p.support_dropLast hp.not_nil]
    exact hz
  have hzt : z ∈ p.support.tail :=
    p.tail_support_perm_dropLast_support.mem_iff.mpr hz'
  have hzf : z ∈ p.darts.map (fun d => d.fst) := by rwa [Walk.map_fst_darts]
  have hzs : z ∈ p.darts.map (fun d => d.snd) := by rwa [Walk.map_snd_darts]
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hzf
  obtain ⟨e,he',hee⟩ := List.mem_map.mp hzs
  exact ⟨by rw [← hee,hs e he']; exact (hprojMap e).2,
    by rw [← he,ht d hd]; exact (hprojMap d).1⟩

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Templates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem demand_load_le_degree {V : Type cycleUniverse3} {I : Type cycleUniverse4} {B : Type cycleUniverse5} [Fintype V] [Fintype I]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : B → Set (Sym2 V))
    (hE : Pairwise fun b c => Disjoint (E b) (E c))
    (owner : I → B) (x y : I → V)
    (hunique : ∀ i j v, owner i = owner j →
      (x i = v ∨ y i = v) → (x j = v ∨ y j = v) → i = j)
    (hedge : ∀ i v, x i = v ∨ y i = v →
      ∃ w, G.Adj v w ∧ s(v,w) ∈ E (owner i)) (v : V) :
    demandLoad x y v ≤ G.degree v := by
  classical
  let S := {i : I // x i = v ∨ y i = v}
  have hs (i : S) := hedge i.val v i.property
  let f : S → G.neighborFinset v := fun i =>
    ⟨(hs i).choose, by simpa using (hs i).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : (hs i).choose = (hs j).choose := congrArg Subtype.val hij
    apply Subtype.ext
    by_cases ho : owner i.val = owner j.val
    · exact hunique i.val j.val v ho i.property j.property
    · exact False.elim (Set.disjoint_left.mp (hE ho)
        (hs i).choose_spec.2 (by rw [he]; exact (hs j).choose_spec.2))
  have hc := Fintype.card_le_of_injective f hf
  have hn : Fintype.card (G.neighborFinset v) = G.degree v := by
    rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
  rw [hn] at hc
  have hcS : Fintype.card S = demandLoad x y v := by
    simp only [S, Fintype.card_subtype, demandLoad]
    congr 1
    ext i
    simp
  rw [hcS] at hc
  exact hc

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch

noncomputable section
open SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

theorem edgeDecomposition_assemble {V I : Type} [Fintype I] (G : SimpleGraph V)
    (W : I → Type) (H : ∀ i, SimpleGraph (W i))
    (f : ∀ i, H i →g G) (hf : ∀ i, Function.Injective (f i))
    (hdisj : Pairwise (fun i j =>
      Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
    (hcover : (⋃ i, Sym2.map (f i) '' (H i).edgeSet) = G.edgeSet)
    (k : I → ℕ) (hparts : ∀ i, EdgeDecomposition (H i) (k i)) :
    EdgeDecomposition G (∑ i, k i) := by
  classical
  choose parts hp hd hu using hparts
  let J := Σ i, Fin (k i)
  let P : J → Set (Sym2 V) := fun j => Sym2.map (f j.1) '' parts j.1 j.2
  have hpart : ∀ j, CycleOrSingleEdge G (P j) := by
    intro j; exact cycleOrSingleEdge_map (f j.1) (hf j.1) (hp j.1 j.2)
  have hsub : ∀ i a, parts i a ⊆ (H i).edgeSet := by
    intro i a; exact cycleOrSingleEdge_subset (hp i a)
  have hdisjP : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases h : i = j
    · subst j
      have hab : a ≠ b := fun he => hij (by cases he; rfl)
      apply Set.disjoint_left.mpr
      rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
      have hxy : x = y := Sym2.map.injective (hf i) (he.trans he'.symm)
      subst y
      exact Set.disjoint_left.mp (hd i hab) hx hy
    · exact (hdisj h).mono (Set.image_mono (hsub i a)) (Set.image_mono (hsub j b))
  have hcoverP : (⋃ j, P j) = G.edgeSet := by
    rw [← hcover]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,a⟩,x,hx,he⟩
      exact ⟨i,x,hsub i a hx,he⟩
    · rintro ⟨i,x,hx,he⟩
      rw [← hu i] at hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i,a⟩,x,ha,he⟩
  have hc : Fintype.card J = ∑ i, k i := by simp [J, Fintype.card_sigma]
  rw [← hc]
  exact edgeDecomposition_of_indexed G P hpart hdisjP hcoverP

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma edgeDecomposition_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f)
    (hu : Sym2.map f '' H.edgeSet = G.edgeSet) {k : ℕ} (hk : EdgeDecomposition H k) :
    EdgeDecomposition G k := by
  have := edgeDecomposition_assemble (I := Unit) G (fun _ : Unit => W) (fun _ => H) (fun _ => f)
    (fun _ => hf) (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
    (by rw [Set.iUnion_const]; exact hu) (fun _ => k) (fun _ => hk)
  simpa using this

lemma edgeDecomposition_on {V : Type} (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A)
    {k : ℕ} (hk : EdgeDecomposition (G.induce (A:Set V)) k) : EdgeDecomposition G k := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  apply edgeDecomposition_map f Subtype.val_injective _ hk
  ext e
  constructor
  · rintro ⟨e,he,rfl⟩
    induction e using Sym2.ind with | _ x y => exact he
  · intro he
    induction e using Sym2.ind with
    | _ x y => exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma endpointLoad_subtype_le {V I : Type} [Fintype I]
    (x y : I → V) (s : I → Prop) (v : V) :
    endpointLoad univ (fun i : {i // s i} => x i) (fun i => y i) v ≤ endpointLoad univ x y v := by
  classical
  simp only [endpointLoad]
  apply Finset.card_le_card_of_injOn (fun i : {i // s i} => i.val)
  · intro i hi; simpa using hi
  · intro i _ j _ h; exact Subtype.ext h

theorem uniform_multi_batch_routing :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R I T : Type) [Fintype V] [Fintype R] [Fintype I],
      ∀ (G : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      (∀ r, P r ≤ G) → Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (owner : I → R) (x y : I → V),
      (∀ i, x i ∈ U (owner i) ∧ y i ∈ U (owner i) ∧ x i ≠ y i) →
      ∀ (team : I → T) (Z : I → Finset V),
      (∀ v, (endpointLoad univ x y v:ℝ) ≤ D^(1/100:ℝ)) →
      (∀ i, ((univ.filter (fun j => team j = team i)).card:ℝ) ≤ D^(3/10:ℝ)) →
      (∀ i, ((Z i).card:ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (∀ v ∈ (q i).support, v ∈ U (owner i)) ∧
          (q i).edgeSet ⊆ (P (owner i)).edgeSet ∧ Disjoint (pathInterior (q i)) (Z i)) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  obtain ⟨D₀,hD₀,hroute⟩ := uniform_batch_routing
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R I T _ _ _ G P U hPG hPP hUU he hr owner x y hxy team Z hl ht hZ
  let J := fun r => {i // owner i = r}
  have hex : ∀ r, ∃ q : ∀ i : J r, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (∀ v ∈ (q i).support, v ∈ U r) ∧
        (q i).edgeSet ⊆ (P r).edgeSet ∧ Disjoint (pathInterior (q i)) (Z i)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      (∀ i j : J r, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
    intro r
    obtain ⟨q,hq,hd,hi⟩ := hroute D hD V G (P r) (hPG r) (U r) (he r) (hr r).1 (hr r).2
      (J r) T (fun i => x i) (fun i => y i)
      (fun i => by simpa only [← i.property] using (hxy i).1)
      (fun i => by simpa only [← i.property] using (hxy i).2.1)
      (fun i => (hxy i).2.2) (fun i => team i) (fun i => Z i)
      (fun v => (show (endpointLoad univ (fun i : J r => x i) (fun i => y i) v:ℝ) ≤
        endpointLoad univ x y v by exact_mod_cast endpointLoad_subtype_le x y (fun i => owner i = r) v).trans (hl v))
      (fun i => le_trans (by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card_of_injOn (fun i : J r => i.val)
        · intro j hj; simpa using hj
        · intro j _ l _ h; exact Subtype.ext h) (ht i)) (fun i => hZ i)
    exact ⟨q,fun i => ⟨(hq i).1,(hq i).2.2⟩,hd,hi⟩
  choose q hq hd hi using hex
  let f : ∀ i, G.Walk (x i) (y i) := fun i => q (owner i) ⟨i,rfl⟩
  have hf (i : I) (r : R) (h : owner i = r) : f i = q r ⟨i,h⟩ := by
    subst r; rfl
  refine ⟨f,fun i => hq _ _,?_,?_⟩
  · intro i j hij
    by_cases hh : owner i = owner j
    · have h := hd (owner i) (show (⟨i,rfl⟩:J (owner i)) ≠ ⟨j,hh.symm⟩ from
        fun h => hij (congrArg Subtype.val h))
      rw [hf j (owner i) hh.symm]
      exact h
    · exact (hPP hh).mono (hq _ _).2.2.1 (hq _ _).2.2.1
  · intro i j hij hteam
    by_cases hh : owner i = owner j
    · have h := hi (owner i) ⟨i,rfl⟩ ⟨j,hh.symm⟩
        (fun h => hij (congrArg Subtype.val h)) hteam
      rw [hf j (owner i) hh.symm]
      exact h
    · apply (hUU hh).mono
      · intro v hv; exact (hq (owner i) ⟨i,rfl⟩).2.1 v (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)
      · intro v hv; exact (hq (owner j) ⟨j,rfl⟩).2.1 v (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)

attribute [instance] CycleOutline.finiteW

namespace CycleOutline
variable {V : Type} {G : SimpleGraph V} (c : CycleOutline G)

lemma vertices_card_support : c.vertices.card ≤ 2 * c.cycle.dropLast.support.toFinset.card := by
  have hfirst : c.vertices.card ≤ 2*c.cycle.darts.toFinset.card := by
    calc
      _ ≤ ∑ d ∈ c.cycle.darts.toFinset, ({(c.rep d).fst,(c.rep d).snd}:Finset V).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ c.cycle.darts.toFinset, 2 := Finset.sum_le_sum (fun d _ => Finset.card_le_two)
      _ = _ := by simp [mul_comm]
  have hd : c.cycle.darts.toFinset.card ≤ c.cycle.dropLast.support.toFinset.card := by
    calc
      _ ≤ c.cycle.darts.length := List.toFinset_card_le _
      _ = c.cycle.dropLast.support.length := by
        rw [Walk.length_darts,Walk.length_support,Walk.length_dropLast]
        have := c.isCycle.three_le_length; omega
      _ = c.cycle.dropLast.support.toFinset.card := (List.toFinset_card_of_nodup c.isCycle.isPath_dropLast.support_nodup).symm
  omega

end CycleOutline
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

attribute [instance] RoutingTemplate.finiteArity

theorem uniform_resolve_templates :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R B : Type) [Fintype V] [Fintype R] [Fintype B],
      ∀ (G F : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      F ≤ G → (∀ r, P r ≤ G) →
      Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, Disjoint F.edgeSet (P r).edgeSet) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (b : B → RoutingTemplate G),
      (∀ j, (b j).edges ⊆ F.edgeSet) →
      Pairwise (fun j k => Disjoint (b j).edges (b k).edges) →
      ∀ owner : (j : B) → (b j).Arity → R,
      (∀ j i, (b j).x i ∈ U (owner j i) ∧ (b j).y i ∈ U (owner j i)) →
      (∀ j i, (F.degree ((b j).x i):ℝ) ≤ D^(1/100:ℝ) ∧
        (F.degree ((b j).y i):ℝ) ≤ D^(1/100:ℝ)) →
      (∀ j, (Fintype.card (b j).Arity:ℝ) ≤ D^(3/10:ℝ)) →
      (∀ j, ((b j).vertices.card:ℝ) ≤ 2*D^(3/10:ℝ)) →
      ∃ (parts : B → Set (Sym2 V)) (used : Set (Sym2 V)),
        (∀ j, CycleOrSingleEdge G (parts j)) ∧
        Pairwise (fun j k => Disjoint (parts j) (parts k)) ∧
        used ⊆ ⋃ r, (P r).edgeSet ∧ Disjoint F.edgeSet used ∧
        (⋃ j, parts j) = (⋃ j, (b j).edges) ∪ used := by
  classical
  obtain ⟨D₀,hD₀,hr⟩ := uniform_multi_batch_routing
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R B _ _ _ G F P U hFG hPG hPP hUU hFP he hsize b hsub hdis owner hends hdeg hnum hvertices
  let I := Σ j, (b j).Arity
  let x : I → V := fun i => (b i.1).x i.2
  let y : I → V := fun i => (b i.1).y i.2
  have hl (v : V) : (endpointLoad univ x y v:ℝ) ≤ D^(1/100:ℝ) := by
    have hload : endpointLoad univ x y v ≤ F.degree v := by
      have hh := demand_load_le_degree F (fun j => (b j).edges) hdis
        Sigma.fst x y (by
          rintro ⟨j,i⟩ ⟨k,l⟩ v h h₁ h₂
          dsimp only at h; subst k
          congr 1; exact (b j).unique i l v h₁ h₂) (by
          rintro ⟨j,i⟩ v h
          obtain ⟨w,hw⟩ := (b j).incident i v h
          exact ⟨w,hsub j hw,hw⟩) v
      simpa [demandLoad,endpointLoad] using hh
    by_cases hz : endpointLoad univ x y v = 0
    · rw [hz,Nat.cast_zero]; exact Real.rpow_nonneg (by linarith) _
    · have hp : 0 < (univ.filter fun i => x i = v ∨ y i = v).card := by
        change 0 < endpointLoad univ x y v; omega
      obtain ⟨⟨j,i⟩,hi⟩ := Finset.card_pos.mp hp
      have hv : (b j).x i = v ∨ (b j).y i = v := (Finset.mem_filter.mp hi).2
      have hh : (F.degree v:ℝ) ≤ D^(1/100:ℝ) := by
        rcases hv with rfl | rfl
        · exact (hdeg j i).1
        · exact (hdeg j i).2
      exact (Nat.cast_le.mpr hload).trans hh
  have hteam (i : I) : ((univ.filter fun j : I => j.1 = i.1).card:ℝ) ≤ D^(3/10:ℝ) := by
    have hc : (univ.filter fun j : I => j.1 = i.1).card = Fintype.card (b i.1).Arity := by
      rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sigma]
      calc
        _ = ∑ j : B, if j = i.1 then Fintype.card (b j).Arity else 0 := by
          apply Finset.sum_congr rfl; intro j _
          by_cases hh : j = i.1 <;> simp [hh]
        _ = _ := by simp
    rw [hc]; exact hnum i.1
  obtain ⟨q,hq,hqd,hqi⟩ := hr D hD V R I B G P U hPG hPP hUU he hsize
    (fun i => owner i.1 i.2) x y (fun i => ⟨(hends i.1 i.2).1,(hends i.1 i.2).2,(b i.1).ne i.2⟩)
    Sigma.fst (fun i => (b i.1).vertices) hl hteam (fun i => hvertices i.1)
  let used := ⋃ i, (q i).edgeSet
  let parts := fun j => (b j).edges ∪ ⋃ i, (q ⟨j,i⟩).edgeSet
  have hu : used ⊆ ⋃ r, (P r).edgeSet := by
    apply Set.iUnion_subset; intro i
    exact Set.subset_iUnion_of_subset (owner i.1 i.2) (hq i).2.2.1
  have hFu : Disjoint F.edgeSet used := by
    refine Set.disjoint_iUnion_right.mpr (fun i => ?_)
    exact (hFP _).mono_right (hq i).2.2.1
  have hbu : ∀ j, Disjoint (b j).edges used := fun j => hFu.mono_left (hsub j)
  refine ⟨parts,used,?_,?_,hu,hFu,?_⟩
  · intro j
    exact (b j).complete (fun i => q ⟨j,i⟩) (fun i => (hq _).1) (fun i => (hq _).2.2.2)
      (fun i l hil => hqi _ _ (fun h => hil (eq_of_heq (Sigma.mk.inj_iff.mp h).2)) rfl)
  · intro j k hjk
    apply Set.disjoint_union_left.mpr; constructor
    · apply Set.disjoint_union_right.mpr; constructor
      · exact hdis hjk
      · exact (hbu j).mono_right (Set.iUnion_subset (fun i => Set.subset_iUnion (fun z : I => (q z).edgeSet) ⟨k,i⟩))
    · apply Set.disjoint_union_right.mpr; constructor
      · exact ((hbu k).mono_right (Set.iUnion_subset (fun i => Set.subset_iUnion (fun z : I => (q z).edgeSet) ⟨j,i⟩))).symm
      · apply Set.disjoint_iUnion_left.mpr; intro i
        apply Set.disjoint_iUnion_right.mpr; intro l
        exact hqd (fun h => hjk (congrArg Sigma.fst h))
  · ext e
    simp only [parts,used,Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨j,he|⟨i,hi⟩⟩
      · exact Or.inl ⟨j,he⟩
      · exact Or.inr ⟨⟨j,i⟩,hi⟩
    · rintro (⟨j,he⟩|⟨⟨j,i⟩,he⟩)
      · exact ⟨j,Or.inl he⟩
      · exact ⟨j,Or.inr ⟨i,he⟩⟩

end
end ErdosGallai.Batch
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.BatchResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem cycle_template_of_representatives_bounded {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle)
    (M : ℕ) (hM : p.dropLast.support.toFinset.card ≤ M) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ p.edgeSet} ∧
      Fintype.card b.Arity ≤ M ∧
      b.vertices.card ≤ 2*M ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  classical
  obtain ⟨R,hR⟩ := orient_edge_representatives projMap S hSG (fun e he =>
    (hrep e he).exists)
  let v₀ := (R ⟨(a,p.snd),p.adj_snd hp.not_nil⟩).fst
  obtain ⟨s,t,hports,hproj⟩ := choose_cycle_ports projMap R (fun d => (hR d).2) p hp v₀
  have hfst (d : Q.Dart) (hd : d ∈ p.darts) : d.fst ∈ p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil,← Walk.map_fst_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  have hsnd (d : Q.Dart) (hd : d ∈ p.darts) : d.snd ∈ p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil]
    apply p.tail_support_perm_dropLast_support.mem_iff.mp
    rw [← Walk.map_snd_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  let c : CycleOutline G := {
    W := W, finiteW := inferInstance, Q := Q, base := a, cycle := p, isCycle := hp,
    rep := R, start := fun z => if z ∈ p.dropLast.support then s z else v₀,
    finish := fun z => if z ∈ p.dropLast.support then t z else v₀,
    project := projMap,
    ports := by intro d hd; simpa only [ite_eq_left (hfst d hd),ite_eq_left (hsnd d hd)] using hports d hd,
    projects := by intro z hz; simpa only [ite_eq_left hz] using hproj z hz,
    outside := by intro z hz; simp only [ite_eq_right hz]
  }
  have hmap (d : Q.Dart) : Sym2.map projMap (R d).edge = d.edge := by
    change s(projMap (R d).fst,projMap (R d).snd) = s(d.fst,d.snd)
    rw [(hR d).2.1,(hR d).2.2]
  have he : c.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ p.edgeSet} := by
    ext e
    constructor
    · rintro ⟨d,hd,rfl⟩
      refine ⟨(hR d).1,?_⟩
      rw [hmap]
      change d.edge ∈ p.edges
      rw [Walk.edges_eq_map_darts]
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    · rintro ⟨hS,he⟩
      change Sym2.map projMap e ∈ p.edges at he
      rw [Walk.edges_eq_map_darts] at he
      obtain ⟨d,hd,hde⟩ := List.mem_map.mp he
      refine ⟨d,hd,?_⟩
      exact (hrep d.edge d.edge_mem).unique ⟨hS,hde.symm⟩ ⟨(hR d).1,hmap d⟩
  refine ⟨RoutingTemplate.ofCycle c,he,?_,?_,?_⟩
  · change Fintype.card c.Switch ≤ M
    apply le_trans _ hM
    apply Finset.card_le_card_of_injOn (fun i : c.Switch => i.val)
    · intro z hz; exact List.mem_toFinset.mpr z.property.1
    · intro z _ w _ h; exact Subtype.ext h
  · exact c.vertices_card_support.trans (Nat.mul_le_mul_left _ hM)
  · intro i
    change c.Switch at i
    exact (c.projects i i.property.1).1.trans (c.projects i i.property.1).2.symm

theorem quotient_part_template_on {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (A : Finset W) (hA : ∀ ⦃x y⦄, Q.Adj x y → x ∈ A ∧ y ∈ A)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    (s : Set (Sym2 W)) (hs : CycleOrSingleEdge Q s) :
    ∃ b : RoutingTemplate G,
      b.edges = {e | e ∈ S ∧ Sym2.map projMap e ∈ s} ∧
      Fintype.card b.Arity ≤ A.card ∧
      b.vertices.card ≤ 2*A.card ∧
      ∀ i, projMap (b.x i) = projMap (b.y i) := by
  rcases hs with ⟨a,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact cycle_template_of_representatives_bounded projMap S hSG hrep p hp A.card (by
      apply Finset.card_le_card
      intro z hz
      rw [List.mem_toFinset,p.support_dropLast hp.not_nil,← Walk.map_fst_darts] at hz
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hz
      exact (hA d.adj).1)
  · obtain ⟨f,hf,huniq⟩ := hrep e he
    refine ⟨RoutingTemplate.ofSingle f (hSG hf.1),?_,by change Fintype.card Empty ≤ _; simp,by simp [RoutingTemplate.ofSingle],fun i => i.elim⟩
    ext g
    change g = f ↔ g ∈ S ∧ Sym2.map projMap g ∈ ({e} : Set (Sym2 W))
    constructor
    · intro h; subst g; exact ⟨hf.1,hf.2⟩
    · rintro ⟨hg,hge⟩; exact huniq g ⟨hg,hge⟩

theorem quotient_partition_templates_on {V W : Type} [Fintype W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (projMap : V → W)
    (S : Set (Sym2 V)) (hSG : S ⊆ G.edgeSet)
    (A : Finset W) (hA : ∀ ⦃x y⦄, Q.Adj x y → x ∈ A ∧ y ∈ A)
    (himage : Sym2.map projMap '' S = Q.edgeSet)
    (hrep : ∀ e ∈ Q.edgeSet, ∃! f, f ∈ S ∧ Sym2.map projMap f = e)
    {k : ℕ} (hQ : EdgeDecomposition Q k) :
    ∃ b : Fin k → RoutingTemplate G,
      Pairwise (fun i j => Disjoint (b i).edges (b j).edges) ∧
      (⋃ i, (b i).edges) = S ∧
      (∀ i, Fintype.card (b i).Arity ≤ A.card ∧
        (b i).vertices.card ≤ 2*A.card ∧
        ∀ j, projMap ((b i).x j) = projMap ((b i).y j)) := by
  classical
  obtain ⟨parts,hp,hd,hcover⟩ := hQ
  choose b hb hnum hv hprojMap using fun i => quotient_part_template_on projMap S hSG A hA hrep (parts i) (hp i)
  refine ⟨b,?_,?_,fun i => ⟨hnum i,hv i,hprojMap i⟩⟩
  · intro i j hij
    rw [hb i,hb j]
    exact Set.disjoint_left.mpr (fun _ hi hj => Set.disjoint_left.mp (hd hij) hi.2 hj.2)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; rw [hb i] at hi; exact hi.1
    · intro he
      have hq : Sym2.map projMap e ∈ Q.edgeSet := by rw [← himage]; exact Set.mem_image_of_mem _ he
      rw [← hcover] at hq
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
      exact ⟨i,by rw [hb i]; exact ⟨he,hi⟩⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walk_support_on {V : Type} {G : SimpleGraph V} (W : Finset V)
    (hW : ∀ ⦃x y⦄, G.Adj x y → x ∈ W ∧ y ∈ W)
    {x y : V} (p : G.Walk x y) (hp : 0 < p.length) : p.support.toFinset ⊆ W := by
  classical
  intro v hv
  obtain ⟨e,he,hv⟩ := Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (p := p) (by simpa only [Walk.length_eq_zero_iff.symm] using (Nat.ne_of_gt hp)) |>.mp (List.mem_toFinset.mp hv)
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := p.edges_subset_edgeSet he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact (hW hab).1
    · exact (hW hab).2

attribute [instance] BatchTemplateFamily.finiteIndex

lemma BatchTemplateFamily.subset {V I : Type} [Fintype I]
    {G J : SimpleGraph V} {X : I → Finset V} {W bad k}
    (b : BatchTemplateFamily G J X W bad k) (i : b.Index) : (b.block i).edges ⊆ J.edgeSet := by
  rw [← b.cover]
  intro e he; exact Or.inr (Set.mem_iUnion.mpr ⟨i,he⟩)

theorem prepare_templates {V I : Type} [Fintype V] [Fintype I]
    (G J : SimpleGraph V) (hJG : J ≤ G) (W : Finset V)
    (hW : ∀ ⦃x y⦄, J.Adj x y → x ∈ W ∧ y ∈ W)
    (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (hX : ∀ i, X i ⊆ W) (b : PreparedBatch J X hd)
    {k : ℕ} (hk : EdgeDecomposition b.quotient k) :
    Nonempty (BatchTemplateFamily G J X W b.bad k) := by
  classical
  let projMap := familyProject X hd b.pairing
  let A := W.image projMap
  have hAW : A.card ≤ W.card := Finset.card_image_le
  obtain ⟨q,hqd,hqu,hqn⟩ := quotient_partition_templates_on projMap (b.retained:Set (Sym2 V))
    (b.retained_subset.trans (SimpleGraph.edgeSet_mono hJG)) A (b.quotient_supported W hW)
    b.quotient_edges.symm (by simpa only [Finset.mem_coe] using b.representatives) hk
  have hqsub (j) : (q j).edges ⊆ (b.retained : Set (Sym2 V)) := by
    rw [← hqu]; intro e he; exact Set.mem_iUnion.mpr ⟨j,he⟩
  have hex (j) (i : (q j).Arity) : ∃ r, (q j).x i ∈ X r ∧ (q j).y i ∈ X r := by
    obtain he | ⟨r,hx,hy,_⟩ := (familyProject_eq_iff X hd b.pairing _ _).mp ((hqn j).2.2 i)
    · exact False.elim ((q j).ne i he)
    · exact ⟨r,hx,hy⟩
  choose own hown using hex
  let P := {z : Σ i, Fin (b.count i) // 0 < (b.path z.1 z.2).walk.length}
  let path : ∀ z : P, G.Walk (b.path z.1.1 z.1.2).start (b.path z.1.1 z.1.2).finish :=
    fun z => (b.path z.1.1 z.1.2).walk.map (SimpleGraph.Hom.ofLE hJG)
  have hpe (z : P) : (path z).edgeSet = (b.path z.1.1 z.1.2).walk.edgeSet := by
    simp [path,Walk.edgeSet_map,SimpleGraph.Hom.ofLE]
  have hps (z : P) : (path z).IsPath := (b.path z.1.1 z.1.2).simple.map Function.injective_id
  have hpl (z : P) : 2 ≤ (path z).length := by
    simpa only [path,Walk.length_map] using (b.ends z.1.1 z.1.2 z.property).2.2
  let t : P → RoutingTemplate G := fun z => RoutingTemplate.ofPath (path z) (hps z) (hpl z)
  have hte (z : P) : (t z).edges = (b.path z.1.1 z.1.2).walk.edgeSet := hpe z
  have htv (z : P) : (t z).vertices.card ≤ W.card := by
    apply Finset.card_le_card
    change (path z).support.toFinset ⊆ W
    simpa [path,Walk.support_map,SimpleGraph.Hom.ofLE] using
      walk_support_on W hW (b.path z.1.1 z.1.2).walk z.property
  have hta (z : P) : Fintype.card (t z).Arity ≤ W.card := by
    change Fintype.card Unit ≤ W.card
    simpa using Finset.card_pos.mpr ⟨(b.path z.1.1 z.1.2).start,
      hX z.1.1 (b.ends z.1.1 z.1.2 z.property).1⟩
  have htu : (⋃ z, (t z).edges) = ⋃ i, ⋃ j, (b.path i j).walk.edgeSet := by
    ext e; simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z,hz⟩; exact ⟨z.1.1,z.1.2,(hte z) ▸ hz⟩
    · rintro ⟨i,j,hj⟩
      have hp : 0 < (b.path i j).walk.length := by
        by_contra h
        have hn := Walk.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
        have he := Walk.edges_eq_nil.mpr hn
        change e ∈ (b.path i j).walk.edges at hj
        rw [he] at hj; contradiction
      exact ⟨⟨⟨i,j⟩,hp⟩,by rw [hte]; exact hj⟩
  refine ⟨{
    Index := Fin k ⊕ P,
    finiteIndex := inferInstance,
    block := Sum.elim q t,
    count := ?_,
    disjoint := ?_,
    bad_disjoint := ?_,
    cover := ?_,
    arity := ?_,
    vertices := ?_,
    owner := fun j => match j with | Sum.inl j => own j | Sum.inr z => fun _ => z.1.1,
    ends := ?_
  }⟩
  · have hp : Fintype.card P ≤ 2 * ∑ i, (X i).card := by
      calc
        _ ≤ Fintype.card (Σ i, Fin (b.count i)) := Fintype.card_subtype_le _
        _ = ∑ i, b.count i := by simp
        _ ≤ ∑ i, 2*(X i).card := Finset.sum_le_sum (fun i _ => b.count_le i)
        _ = _ := by rw [← Finset.mul_sum]
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_left hp k
  · intro j l hne
    rcases j with j | j <;> rcases l with l | l <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact hqd (fun h => hne (congrArg Sum.inl h))
    · exact (b.retained_paths l.1.1 l.1.2).mono (hqsub j) (by rw [hte])
    · exact ((b.retained_paths j.1.1 j.1.2).mono (hqsub l) (by rw [hte])).symm
    · rw [hte,hte]
      exact b.paths_disjoint (fun h => hne (congrArg Sum.inr (Subtype.ext h)))
  · rintro (j | z) <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact b.bad_retained.mono_right (hqsub j)
    · rw [hte]; exact b.bad_paths _ _
  ·
    simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]
    rw [hqu,htu,← Set.union_assoc]
    exact b.cover
  · rintro (j | z)
    · exact (hqn j).1.trans hAW
    · exact hta z
  · rintro (j | z)
    · exact (hqn j).2.1.trans (Nat.mul_le_mul_left _ hAW)
    · exact (htv z).trans (by omega)
  · rintro (j | z) i
    · exact hown j i
    · exact ⟨(b.ends z.1.1 z.1.2 z.property).2.1,(b.ends z.1.1 z.1.2 z.property).1⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem uniform_batch_resolution :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V R B : Type) [Fintype V] [Fintype R] [Fintype B],
      ∀ (G F : SimpleGraph V) (P : R → SimpleGraph V) (U : R → Finset V),
      F ≤ G → (∀ r, P r ≤ G) →
      Pairwise (fun r s => Disjoint (P r).edgeSet (P s).edgeSet) →
      Pairwise (fun r s => Disjoint (U r) (U s)) →
      (∀ r, Disjoint F.edgeSet (P r).edgeSet) →
      (∀ r, CutExpansionOn (P r) (U r) (D^(9/10:ℝ)/4)) →
      (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
      ∀ (J : B → SimpleGraph V) (W : B → Finset V),
      (∀ b, J b ≤ F) → Pairwise (fun b c => Disjoint (J b).edgeSet (J c).edgeSet) →
      (⋃ b, (J b).edgeSet) = F.edgeSet →
      (∀ b, ∀ ⦃x y⦄, (J b).Adj x y → x ∈ W b ∧ y ∈ W b) →
      (∀ b, ((W b).card:ℝ) ≤ D^(3/10:ℝ)) →
      ∀ (I : B → Type) [∀ b, Fintype (I b)] (X : ∀ b, I b → Finset V)
        (hXd : ∀ b, Pairwise fun i j => Disjoint (X b i) (X b j)),
      (∀ b i, X b i ⊆ W b) →
      ∀ rX : ∀ b, I b → R,
      (∀ b i, X b i ⊆ U (rX b i)) →
      (∀ b i v, v ∈ X b i → (F.degree v:ℝ) ≤ D^(1/100:ℝ)) →
      ∀ (prep : ∀ b, PreparedBatch (J b) (X b) (hXd b)) (k : B → ℕ),
      (∀ b, EdgeDecomposition (prep b).quotient (k b)) →
      ∃ (K : Type) (_ : Fintype K) (parts : K → Set (Sym2 V)) (used : Set (Sym2 V)),
        Fintype.card K ≤ (∑ b, k b) + 8 * ∑ b, ∑ i, (X b i).card ∧
        (∀ j, CycleOrSingleEdge G (parts j)) ∧
        Pairwise (fun j l => Disjoint (parts j) (parts l)) ∧
        used ⊆ ⋃ r, (P r).edgeSet ∧ Disjoint F.edgeSet used ∧
        (⋃ j, parts j) = F.edgeSet ∪ used := by
  classical
  obtain ⟨D₀,hD₀,hresolve⟩ := uniform_resolve_templates
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V R B _ _ _ G F P U hFG hPG hPP hUU hFP he hr J W hJF hJJ hJu hW hWnum I _ X hXd hXW rX hXU hdeg prep k hk
  have hT (b : B) := prepare_templates G (J b) ((hJF b).trans hFG) (W b) (hW b)
    (X b) (hXd b) (hXW b) (prep b) (hk b)
  let T : ∀ b, BatchTemplateFamily G (J b) (X b) (W b) (prep b).bad (k b) :=
    fun b => Classical.choice (hT b)
  let Q := Σ b, (T b).Index
  let q : Q → RoutingTemplate G := fun z => (T z.1).block z.2
  have hqsub (z : Q) : (q z).edges ⊆ F.edgeSet :=
    ((T z.1).subset z.2).trans (SimpleGraph.edgeSet_mono (hJF z.1))
  have hqd : Pairwise fun z w : Q => Disjoint (q z).edges (q w).edges := by
    rintro ⟨b,i⟩ ⟨c,j⟩ hne
    by_cases hh : b = c
    · subst c; exact (T b).disjoint (fun h => hne (by cases h; rfl))
    · exact (hJJ hh).mono ((T b).subset i) ((T c).subset j)
  let owner : (z : Q) → (q z).Arity → R := fun z i => rX z.1 ((T z.1).owner z.2 i)
  obtain ⟨parts,used,hparts,hpartsd,hused,hFu,hcover⟩ :=
    hresolve D hD V R Q G F P U hFG hPG hPP hUU hFP he hr q hqsub hqd owner
      (fun z i => ⟨hXU _ _ ((T z.1).ends z.2 i).1,hXU _ _ ((T z.1).ends z.2 i).2⟩)
      (fun z i => ⟨hdeg _ _ _ ((T z.1).ends z.2 i).1,hdeg _ _ _ ((T z.1).ends z.2 i).2⟩)
      (fun z => (Nat.cast_le.mpr ((T z.1).arity z.2)).trans (hWnum z.1))
      (fun z => (Nat.cast_le.mpr ((T z.1).vertices z.2)).trans (by
        push_cast; exact mul_le_mul_of_nonneg_left (hWnum z.1) (by norm_num)))
  let S := Σ b, (prep b).bad
  let e : S → Sym2 V := fun z => z.2.val
  have hSsub (z : S) : e z ∈ (J z.1).edgeSet := (prep z.1).bad_subset z.2.property
  have hSF (z : S) : e z ∈ F.edgeSet := SimpleGraph.edgeSet_mono (hJF z.1) (hSsub z)
  have hinj : Function.Injective e := by
    rintro ⟨b,i⟩ ⟨c,j⟩ h
    by_cases hh : b = c
    · subst c; exact Sigma.ext rfl (heq_of_eq (Subtype.ext h))
    · exact False.elim (Set.disjoint_left.mp (hJJ hh) (hSsub ⟨b,i⟩) (h ▸ hSsub ⟨c,j⟩))
  have hbadq (z : S) (w : Q) : e z ∉ (q w).edges := by
    intro hw
    by_cases hh : z.1 = w.1
    · rcases z with ⟨b,z⟩; rcases w with ⟨c,w⟩
      dsimp only at hh; subst c
      exact Set.disjoint_left.mp ((T b).bad_disjoint w) z.property hw
    · exact Set.disjoint_left.mp (hJJ hh) (hSsub z) ((T w.1).subset w.2 hw)
  have hbadpart (z : S) (w : Q) : e z ∉ parts w := by
    intro hw
    have hu : e z ∈ ⋃ w, parts w := Set.mem_iUnion.mpr ⟨w,hw⟩
    rw [hcover] at hu
    rcases hu with hu | hu
    · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hu; exact hbadq z w hw
    · exact Set.disjoint_left.mp hFu (hSF z) hu
  have horiginal : (⋃ z : S, {e z}) ∪ (⋃ w : Q, (q w).edges) = F.edgeSet := by
    rw [← hJu]
    ext f
    simp only [Set.mem_union,Set.mem_iUnion,Set.mem_singleton_iff]
    constructor
    · rintro (⟨z,hz⟩ | ⟨w,hw⟩)
      · exact ⟨z.1,hz ▸ hSsub z⟩
      · exact ⟨w.1,(T w.1).subset w.2 hw⟩
    · rintro ⟨b,hb⟩
      rw [← (T b).cover] at hb
      rcases hb with hb | hb
      · exact Or.inl ⟨⟨b,⟨f,hb⟩⟩,rfl⟩
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
        exact Or.inr ⟨⟨b,j⟩,hj⟩
  refine ⟨Q ⊕ S,inferInstance,Sum.elim parts (fun z => {e z}),used,?_,?_,?_,hused,hFu,?_⟩
  · have hq : Fintype.card Q ≤ (∑ b, k b) + 2*∑ b, ∑ i, (X b i).card := by
      calc
        _ = ∑ b, Fintype.card (T b).Index := Fintype.card_sigma
        _ ≤ ∑ b, (k b + 2 * ∑ i, (X b i).card) := Finset.sum_le_sum (fun b _ => (T b).count)
        _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hs : Fintype.card S ≤ 6*∑ b, ∑ i, (X b i).card := by
      calc
        _ = ∑ b, (prep b).bad.card := by simp [S,Fintype.card_sigma]
        _ ≤ ∑ b, 6*∑ i, (X b i).card := Finset.sum_le_sum (fun b _ => (prep b).bad_le)
        _ = _ := by rw [← Finset.mul_sum]
    rw [Fintype.card_sum]; omega
  · rintro (j | z)
    · exact hparts j
    · exact Or.inr ⟨e z,SimpleGraph.edgeSet_mono hFG (hSF z),rfl⟩
  · rintro (i | i) (j | j) hij <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
    · exact hpartsd (fun h => hij (congrArg Sum.inl h))
    · exact (Set.disjoint_singleton_right).mpr (hbadpart j i)
    · exact (Set.disjoint_singleton_left).mpr (hbadpart i j)
    · exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (hinj h)))
  · simp only [Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]
    rw [hcover]
    calc
      _ = ((⋃ z : S, {e z}) ∪ (⋃ w : Q, (q w).edges)) ∪ used := by
        rw [Set.union_comm ((⋃ w : Q, (q w).edges) ∪ used), Set.union_assoc]
      _ = _ := by rw [horiginal]

end
end ErdosGallai.Batch

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CoupledResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch.Splitting
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

lemma colorIndicator_indep {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) :
    iIndepFun (colorIndicator (V := V) i) (edgeColorMeasure V l) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma colorIndicator_integral {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) (e : Sym2 V) :
    ∫ ω, colorIndicator i e ω ∂edgeColorMeasure V l = 1/(l : ℝ) := by
  have hl := (measurePreserving_eval
    (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
  have hi := hl.integral_comp (f := fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [PMF.integral_eq_sum] at hi
  simpa [edgeColorMeasure, colorIndicator, PMF.uniformOfFintype_apply] using hi

lemma colorGraph_interedges {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S T : Finset V) :
    (colorGraph P ω i).interedges S T =
      (P.interedges S T).filter (fun e => ω s(e.1,e.2) = i) := by
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_filter]
  change (x ∈ S ∧ y ∈ T ∧ (P.Adj x y ∧ ω s(x,y) = i)) ↔ _
  tauto

lemma color_cut_sum (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S : Finset V) :
    (∑ e ∈ (P.interedges S Sᶜ).image (fun e => s(e.1,e.2)), colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
  rw [Finset.sum_image (boundary_sym2_injective P S)]
  simp only [colorIndicator, Finset.sum_boole, colorGraph_interedges]

lemma color_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] (i : Fin l) (S : Finset V) {h : ℝ}
    (hexp : CutExpansion P h) (hS : S.card ≤ Sᶜ.card) :
    (edgeColorMeasure V l).real {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ≤
        exp (-h*S.card/(8*l)) := by
  let E := (P.interedges S Sᶜ).image (fun e => s(e.1,e.2))
  have hcard : E.card = (P.interedges S Sᶜ).card :=
    Finset.card_image_of_injOn (boundary_sym2_injective P S)
  have hl : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  have hcut : h * S.card ≤ (E.card : ℝ) := by
    rw [hcard]
    have he := hexp S
    rwa [min_eq_left (by exact_mod_cast hS)] at he
  have hb := bernoulli_sum_lower_tail (μ := edgeColorMeasure V l) E
    (fun e => measurable_of_finite (colorIndicator i e)) (colorIndicator_indep i)
    (fun e ω => by simp only [colorIndicator]; split <;> simp)
    (1/(l : ℝ)) (by positivity) (colorIndicator_integral i)
  apply (measureReal_mono (show {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ⊆
      {ω | (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2} from ?_)).trans
      (hb.trans ?_)
  · intro ω hω
    change (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2
    rw [show (∑ e ∈ E, colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) from color_cut_sum P ω i S]
    calc
      _ ≤ h*S.card/(2*l) := le_of_lt hω
      _ ≤ (E.card : ℝ)/(2*l) := div_le_div_of_nonneg_right hcut (by positivity)
      _ = _ := by ring
  · apply exp_le_exp.mpr
    have he := div_le_div_of_nonneg_right hcut (show 0 ≤ 8*(l : ℝ) by positivity)
    calc
      _ = -((E.card : ℝ)/(8*l)) := by ring
      _ ≤ -(h*S.card/(8*l)) := neg_le_neg he
      _ = _ := by ring

lemma cutExpansion_of_small_cuts (P : SimpleGraph V) [DecidableRel P.Adj] {h : ℝ}
    (hcut : ∀ S : Finset V, S.Nonempty → S.card ≤ Sᶜ.card →
      h*S.card ≤ ((P.interedges S Sᶜ).card : ℝ)) : CutExpansion P h := by
  intro S
  by_cases he : S = ∅
  · simp [he]
  by_cases hc : Sᶜ = ∅
  · simp [hc]
  by_cases hs : S.card ≤ Sᶜ.card
  · rw [min_eq_left (by exact_mod_cast hs)]
    exact hcut S (Finset.nonempty_iff_ne_empty.mpr he) hs
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
    have hi := hcut Sᶜ (Finset.nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs)
    have hcomm : (P.interedges Sᶜ S).card = (P.interedges S Sᶜ).card := by
      have := P.symm
      exact Rel.card_interedges_comm Sᶜ S
    simpa only [compl_compl, hcomm] using hi

lemma sum_nonempty_subsets_power (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)).erase ∅, q^S.card) =
      (1+q)^(Fintype.card V)-1 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun S : Finset V => q^S.card)
    (Finset.mem_univ (∅ : Finset V))
  have hp := Finset.prod_one_add (s := (Finset.univ : Finset V)) (f := fun _ => q)
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at hp
  simp only [Finset.card_empty, pow_zero] at hs
  linarith

theorem edge_splitting_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h) :
    (edgeColorMeasure V l).real {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ≤
      l * (exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) := by
  let cuts : Finset (Finset V) := Finset.univ.erase ∅
  let B (i : Fin l) (S : Finset V) : Set (Sym2 V → Fin l) :=
    {ω | S.card ≤ Sᶜ.card ∧
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)}
  let q : ℝ := exp (-h/(8*l))
  have cover : {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S := by
    intro ω hω
    rcases hω with ⟨i, hi⟩
    by_contra hn
    apply hi
    apply cutExpansion_of_small_cuts
    intro S hS hs
    have hb : ω ∉ B i S := by
      intro hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hS.ne_empty, Finset.mem_univ _⟩, hm⟩⟩⟩⟩
    have hc : h*S.card/(2*l) ≤ (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
      exact le_of_not_gt (fun hf => hb ⟨hs, hf⟩)
    convert hc using 1 ; ring
  have hbound (i : Fin l) (S : Finset V) :
      (edgeColorMeasure V l).real (B i S) ≤ q^S.card := by
    by_cases hs : S.card ≤ Sᶜ.card
    · calc
        _ ≤ (edgeColorMeasure V l).real {ω |
            (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} :=
          measureReal_mono (fun _ hw => hw.2)
        _ ≤ exp (-h*S.card/(8*l)) := color_cut_lower_tail P i S hexp hs
        _ = q^S.card := by dsimp [q]; rw [← exp_nat_mul]; congr 1; ring
    · have he : B i S = ∅ := by ext ω; simp [B,hs]
      rw [he, measureReal_empty]
      exact pow_nonneg (exp_pos _).le _
  calc
    _ ≤ (edgeColorMeasure V l).real
        (⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S) :=
      measureReal_mono cover (measure_ne_top _ _)
    _ ≤ ∑ i : Fin l, (edgeColorMeasure V l).real (⋃ S ∈ cuts, B i S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i : Fin l, ∑ S ∈ cuts, (edgeColorMeasure V l).real (B i S) :=
      Finset.sum_le_sum (fun _ _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _i : Fin l, ∑ S ∈ cuts, q^S.card := by
      apply Finset.sum_le_sum; intro i _; exact Finset.sum_le_sum (fun S _ => hbound i S)
    _ = (l : ℝ)*((1+q)^(Fintype.card V)-1) := by
      simp only [cuts, sum_nonempty_subsets_power, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ l*(exp ((Fintype.card V : ℝ)*q)-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg l)
      apply sub_le_sub_right
      calc
        _ ≤ (exp q)^(Fintype.card V) :=
          pow_le_pow_left₀ (by dsimp [q]; positivity) (by linarith [add_one_le_exp q]) _
        _ = _ := (exp_nat_mul _ _).symm

theorem edge_splitting_of_error_lt_one (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h)
    (herror : (l : ℝ)*(exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) < 1) :
    ∃ ω : Sym2 V → Fin l,
      (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
      (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
      (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have he := (edge_splitting_failure_bound P hexp).trans_lt herror
  have hh : ∃ ω : Sym2 V → Fin l, ∀ i, CutExpansion (colorGraph P ω i) (h/(2*l)) := by
    by_contra hn
    push Not at hn
    have hall : {ω : Sym2 V → Fin l | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} =
        Set.univ := Set.eq_univ_of_forall hn
    simp only [hall, Measure.real, measure_univ, ENNReal.toReal_one] at he
    exact (lt_irrefl _ he)
  obtain ⟨ω, hω⟩ := hh
  refine ⟨ω, hω, ?_, ?_⟩
  · intro x y
    exact ⟨fun hxy => ⟨ω s(x,y), hxy, rfl⟩, fun ⟨_, hxy, _⟩ => hxy⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with | _ x y =>
      have hi : (colorGraph P ω i).Adj x y := by simpa using hei
      have hj : (colorGraph P ω j).Adj x y := by simpa using hej
      exact hij (hi.2.symm.trans hj.2)

end

open Filter Asymptotics
open scoped Topology

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

lemma edgeSplittingScaleError_tendsto (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    Tendsto (edgeSplittingScaleError c l) atTop (𝓝 0) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have ht := tendsto_monomial_exp_neg_power (51/50) (9/10) (c/(8*l))
    (by norm_num) (by positivity)
  have hh := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l : ℝ)
  unfold edgeSplittingScaleError
  convert hh using 1 <;> norm_num

universe u

theorem edge_splitting_uniform (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ),
      c*D^(9/10 : ℝ) ≤ h → D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) → CutExpansion P h →
      ∃ ω : Sym2 V → Fin l,
        (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
        (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
        (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have : NeZero l := ⟨hl.ne'⟩
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hevent := (edgeSplittingScaleError_tendsto c hc l hl).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ h hh _hrlo hrhi hexp
  apply edge_splitting_of_error_lt_one P hexp
  apply lt_of_le_of_lt _ (hD₀ D hD)
  unfold edgeSplittingScaleError
  apply mul_le_mul_of_nonneg_left _ hlR.le
  apply sub_le_sub_right
  apply exp_le_exp.mpr
  apply mul_le_mul hrhi _ (exp_pos _).le ((Nat.cast_nonneg (Fintype.card V)).trans hrhi)
  apply exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right hh (show 0 ≤ 8*(l : ℝ) by positivity)
  calc
    -h/(8*l) = -(h/(8*l)) := by ring
    _ ≤ -(c*D^(9/10 : ℝ)/(8*l)) := neg_le_neg he
    _ = -(c/(8*l))*D^(9/10 : ℝ) := by ring

end ErdosGallai.Batch.Splitting

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cutExpansionOn_of_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (he : CutExpansion (P.induce (W:Set V)) h) : CutExpansionOn P W h := by
  intro A hA
  let B : Finset (W:Set V) := univ.filter (fun x => x.val ∈ A)
  have him : B.image Subtype.val = A := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩; exact (Finset.mem_filter.mp hy).2
    · intro hx; exact ⟨⟨x,hA hx⟩,by simp [B,hx],rfl⟩
  have hcomp := subtype_image_compl W B
  rw [him] at hcomp
  have hh := he B
  rw [induced_interedges_card,him] at hh
  have hc : B.card = A.card := by rw [← him,Finset.card_image_of_injective _ Subtype.val_injective]
  have hcc : Bᶜ.card = (W \ A).card := by rw [← hcomp,Finset.card_image_of_injective _ Subtype.val_injective]
  simpa only [hc,hcc] using hh

lemma cutExpansionOn_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P Q : SimpleGraph V} [DecidableRel P.Adj] [DecidableRel Q.Adj]
    {W : Finset V} {h : ℝ} (he : CutExpansionOn P W h) (hPQ : P ≤ Q) : CutExpansionOn Q W h := by
  intro A hA
  exact (he A hA).trans (Nat.cast_le.mpr (Finset.card_le_card (by
    intro e he
    simp only [SimpleGraph.mem_interedges_iff] at he ⊢
    exact ⟨he.1,he.2.1,hPQ he.2.2⟩)))

theorem uniform_two_routers_on : ∃ D₀ : ℝ, ∀ D ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (R : SimpleGraph V) (W : Finset V),
    (∀ ⦃x y⦄, R.Adj x y → x ∈ W ∧ y ∈ W) →
    D^(9/10:ℝ) ≤ (W.card:ℝ) → (W.card:ℝ) ≤ D^(51/50:ℝ) →
    CutExpansionOn R W (D^(9/10:ℝ)) →
    ∃ P T : SimpleGraph V, P ≤ R ∧ T ≤ R ∧ Disjoint P.edgeSet T.edgeSet ∧
      P.edgeSet ∪ T.edgeSet = R.edgeSet ∧
      CutExpansionOn P W (D^(9/10:ℝ)/4) ∧ CutExpansionOn T W (D^(9/10:ℝ)/4) := by
  obtain ⟨D₀,hsplit⟩ := Splitting.edge_splitting_uniform 1 (by norm_num) 2 (by norm_num)
  refine ⟨D₀,?_⟩
  intro D hD V _ _ R W hW hlo hhi he
  let R' := R.induce (W:Set V)
  have he' : Splitting.CutExpansion R' (D^(9/10:ℝ)) := cutExpansion_induce R W _ he
  obtain ⟨ω,hω,hcover,hdis⟩ := hsplit D hD (W:Set V) R' (D^(9/10:ℝ))
    (by simp) (by simpa using hlo) (by simpa using hhi) he'
  let f : (W:Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let Q (i : Fin 2) := (Splitting.colorGraph R' ω i).map f
  have hQR (i : Fin 2) : Q i ≤ R := by
    apply (SimpleGraph.map_le_iff_le_comap f _ _).mpr
    exact fun _ _ h => h.1
  have hind (i) : (Q i).induce (W:Set V) = Splitting.colorGraph R' ω i :=
    SimpleGraph.comap_map_eq f _
  have hexp (i) : @CutExpansionOn V _ (Q i) (fun _ _ => Classical.propDecidable _) W (D^(9/10:ℝ)/4) := by
    apply @cutExpansionOn_of_induce V _ _ (Q i) (fun _ _ => Classical.propDecidable _) W
    have hcol : CutExpansion (Splitting.colorGraph R' ω i) (D^(9/10:ℝ)/4) := by simpa only [CutExpansion, Splitting.CutExpansion, Nat.cast_ofNat, show (2:ℝ)*2=4 by norm_num] using hω i
    convert hcol using 1 ; simp only [hind]
  have hQedge (i) : (Q i).edgeSet = Sym2.map (Subtype.val : ↥(W:Set V) → V) ''
      (Splitting.colorGraph R' ω i).edgeSet := SimpleGraph.edgeSet_map f _
  refine ⟨Q 0,Q 1,hQR 0,hQR 1,?_,?_,hexp 0,hexp 1⟩
  · rw [hQedge,hQedge]
    apply Set.disjoint_left.mpr
    rintro e ⟨a,ha,hae⟩ ⟨b,hb,hbe⟩
    have hab := Sym2.map.injective Subtype.val_injective (hae.trans hbe.symm)
    subst b
    exact Set.disjoint_left.mp (hdis 0 1 (by decide)) ha hb
  · apply Set.Subset.antisymm
    · exact Set.union_subset (SimpleGraph.edgeSet_mono (hQR 0)) (SimpleGraph.edgeSet_mono (hQR 1))
    · intro e heR
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : R.Adj x y := heR
        obtain ⟨i,hi⟩ := (hcover ⟨x,(hW hxy).1⟩ ⟨y,(hW hxy).2⟩).mp hxy
        have hm : s(x,y) ∈ (Q i).edgeSet := by
          rw [hQedge]
          exact ⟨s(⟨x,(hW hxy).1⟩,⟨y,(hW hxy).2⟩),hi,rfl⟩
        fin_cases i
        · exact Or.inl hm
        · exact Or.inr hm

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

lemma routerRemainder_edges {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) :
    (routerRemainder R used).edgeSet = R.edgeSet \ used := by
  simp [routerRemainder,SimpleGraph.edgeSet_sdiff]

lemma routerRemainder_le {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) :
    routerRemainder R used ≤ R := fun _ _ h => h.1

lemma protected_le_remainder {V : Type} {R T : SimpleGraph V} {used : Set (Sym2 V)}
    (hTR : T ≤ R) (htu : Disjoint T.edgeSet used) : T ≤ routerRemainder R used := by
  apply SimpleGraph.edgeSet_subset_edgeSet.mp
  rw [routerRemainder_edges]
  exact fun _ he => ⟨SimpleGraph.edgeSet_mono hTR he,fun hu => Set.disjoint_left.mp htu he hu⟩

lemma protected_avoids_used {V A : Type} (R P T : A → SimpleGraph V)
    (hRR : Pairwise fun i j => Disjoint (R i).edgeSet (R j).edgeSet)
    (hPR : ∀ i, P i ≤ R i) (hTR : ∀ i, T i ≤ R i)
    (hTP : ∀ i, Disjoint (T i).edgeSet (P i).edgeSet)
    (used : Set (Sym2 V)) (hu : used ⊆ ⋃ i, (P i).edgeSet) :
    ∀ i, Disjoint (T i).edgeSet used := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he heu
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hu heu)
  by_cases hij : i = j
  · subst j; exact Set.disjoint_left.mp (hTP i) he hj
  · exact Set.disjoint_left.mp (hRR hij) (SimpleGraph.edgeSet_mono (hTR i) he)
      (SimpleGraph.edgeSet_mono (hPR j) hj)

lemma batch_remainder_ledger {V A K : Type} [Fintype V] [Fintype A] [Fintype K]
    (G F : SimpleGraph V) (R : A → SimpleGraph V)
    (hRG : ∀ i, R i ≤ G)
    (hRR : Pairwise fun i j => Disjoint (R i).edgeSet (R j).edgeSet)
    (hFR : ∀ i, Disjoint F.edgeSet (R i).edgeSet)
    (hcover : F.edgeSet ∪ (⋃ i, (R i).edgeSet) = G.edgeSet)
    (parts : K → Set (Sym2 V)) (hp : ∀ k, CycleOrSingleEdge G (parts k))
    (hd : Pairwise fun j k => Disjoint (parts j) (parts k))
    (used : Set (Sym2 V)) (hu : used ⊆ ⋃ i, (R i).edgeSet)
    (hparts : (⋃ k, parts k) = F.edgeSet ∪ used) :
    decompositionCost G ≤ Fintype.card K + ∑ i, decompositionCost (routerRemainder (R i) used) := by
  apply decompositionCost_adjoin_same G parts hp hd (fun i => routerRemainder (R i) used)
    (fun i => (routerRemainder_le _ _).trans (hRG i))
  · intro i j hij
    exact (hRR hij).mono (SimpleGraph.edgeSet_mono (routerRemainder_le _ _))
      (SimpleGraph.edgeSet_mono (routerRemainder_le _ _))
  · intro i k
    rw [routerRemainder_edges]
    apply Set.disjoint_left.mpr
    intro e he hp
    have hpe : e ∈ F.edgeSet ∪ used := hparts ▸ Set.mem_iUnion.mpr ⟨k,hp⟩
    rcases hpe with hpe | hpe
    · exact Set.disjoint_left.mp (hFR i) hpe he.1
    · exact he.2 hpe
  · rw [hparts,← hcover]
    simp_rw [routerRemainder_edges]
    ext e
    simp only [Set.mem_union,Set.mem_iUnion,Set.mem_sdiff]
    constructor
    · rintro ((hf | hu') | ⟨i,hi,_⟩)
      · exact Or.inl hf
      · exact Or.inr (Set.mem_iUnion.mp (hu hu'))
      · exact Or.inr ⟨i,hi⟩
    · rintro (hf | ⟨i,hi⟩)
      · exact Or.inl (Or.inl hf)
      · by_cases he : e ∈ used
        · exact Or.inl (Or.inr he)
        · exact Or.inr ⟨i,hi,he⟩

lemma prepared_quotient_cost {V I : Type} [Fintype V] [Fintype I]
    (J : SimpleGraph V) (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (p : PreparedBatch J X hd) (W : Finset V)
    (hW : ∀ ⦃x y⦄, J.Adj x y → x ∈ W ∧ y ∈ W)
    (hX : ∀ i, X i ⊆ W) (n : ℕ) (M t : ℝ) (_ht : 0 ≤ t) (hn : W.card < n) (hM : (W.card:ℝ) ≤ M)
    (ih : ∀ (A : Type) [Fintype A] (H : SimpleGraph A), Fintype.card A < n → (Fintype.card A:ℝ) ≤ M →
      (decompositionCost H:ℝ) ≤ t * Fintype.card A) :
    ∃ k, EdgeDecomposition p.quotient k ∧
      (k:ℝ) ≤ t * ((W.card:ℝ) - ∑ i, ((X i).card / 2:ℕ)) := by
  classical
  let A := W.image (familyProject X hd p.pairing)
  let H := p.quotient.induce (A:Set (FamilyQuotient X p.pairing))
  have ho : A.card + ∑ i, (X i).card / 2 = W.card := family_quotient_image_order X hd p.pairing W hX
  have hn' : Fintype.card (A:Set (FamilyQuotient X p.pairing)) < n := by simp only [Finset.coe_sort_coe,Fintype.card_coe]; omega
  refine ⟨decompositionCost H,edgeDecomposition_on _ A (p.quotient_supported W hW) (decompositionCost_spec H),?_⟩
  have hc := ih (A:Set (FamilyQuotient X p.pairing)) H hn' (by simp only [Finset.coe_sort_coe,Fintype.card_coe]; exact (Nat.cast_le.mpr (by omega : A.card ≤ W.card)).trans hM)
  simp only [Finset.coe_sort_coe,Fintype.card_coe] at hc
  have heq : (A.card:ℝ) = (W.card:ℝ) - ∑ i, ((X i).card / 2:ℕ) := by
    have hh : (A.card:ℝ) + ∑ i, ((X i).card / 2:ℕ) = W.card := by exact_mod_cast ho
    linarith
  rwa [heq] at hc

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

theorem uniform_coupled_resolution_cost_oai : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ (V A B : Type) [Fintype V] [Fintype A] [Fintype B],
    ∀ (G F : SimpleGraph V) (R : A → SimpleGraph V) (U : A → Finset V),
    F ≤ G → (∀ r, R r ≤ G) →
    Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) →
    Pairwise (fun r s => Disjoint (U r) (U s)) →
    (∀ r, ∀ ⦃x y⦄, (R r).Adj x y → x ∈ U r ∧ y ∈ U r) →
    (∀ r, Disjoint F.edgeSet (R r).edgeSet) →
    F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet →
    (∀ r, CutExpansionOn (R r) (U r) (D^(9/10:ℝ))) →
    (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
    ∀ (J : B → SimpleGraph V) (W : B → Finset V),
    (∀ b, J b ≤ F) → Pairwise (fun b c => Disjoint (J b).edgeSet (J c).edgeSet) →
    (⋃ b, (J b).edgeSet) = F.edgeSet →
    (∀ b, ∀ ⦃x y⦄, (J b).Adj x y → x ∈ W b ∧ y ∈ W b) →
    (∀ b, ((W b).card:ℝ) ≤ D^(3/10:ℝ)) →
    ∀ (I : B → Type) [∀ b, Fintype (I b)] (X : ∀ b, I b → Finset V)
      (_hXd : ∀ b, Pairwise fun i j => Disjoint (X b i) (X b j)),
    (∀ b i, X b i ⊆ W b) →
    ∀ rX : ∀ b, I b → A,
    (∀ b i, X b i ⊆ U (rX b i)) →
    (∀ b i v, v ∈ X b i → (F.degree v:ℝ) ≤ D^(1/100:ℝ)) →
    1 ≤ D^(1/100:ℝ) → (∀ b i, 8 ≤ (X b i).card) →
    (∀ b i, (D^(1/100:ℝ))^2 ≤ (X b i).card) →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → (∀ b, (W b).card < n) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (decompositionCost H:ℝ) ≤ t * Fintype.card Q) →
    ∃ H : A → SimpleGraph V,
      (∀ r, H r ≤ R r) ∧
      (∀ r, CutExpansionOn (H r) (U r) (D^(9/10:ℝ)/4)) ∧
      (decompositionCost G:ℝ) ≤
        t * ((∑ b, ((W b).card:ℝ)) - ∑ b, ∑ i, ((X b i).card / 2:ℕ)) +
        8 * (∑ b, ∑ i, ((X b i).card:ℝ)) + ∑ r, (decompositionCost (H r):ℝ) := by
  obtain ⟨D₁,hsplit⟩ := uniform_two_routers_on
  obtain ⟨D₂,hD₂,hresolve⟩ := uniform_batch_resolution
  refine ⟨max D₁ D₂,lt_of_lt_of_le hD₂ (le_max_right _ _),?_⟩
  intro D hD V A B _ _ _ G F R U hFG hRG hRR hUU hRU hFR hcover he hr
    J W hJF hJJ hJu hW hWnum I _ X hXd hXW rX hXU hdeg ha hm hma n t ht hn ih
  have hs (r : A) := hsplit D ((le_max_left _ _).trans hD) V (R r) (U r)
    (hRU r) (hr r).1 (hr r).2 (he r)
  choose P T hPR hTR hPT hPu hPe hTe using hs
  have hPP : Pairwise fun r s => Disjoint (P r).edgeSet (P s).edgeSet :=
    fun _ _ h => (hRR h).mono (SimpleGraph.edgeSet_mono (hPR _)) (SimpleGraph.edgeSet_mono (hPR _))
  have hp (b : B) : Nonempty (PreparedBatch (J b) (X b) (hXd b)) :=
    prepare_batch (J b) (X b) (hXd b) (D^(1/100:ℝ)) ha (hm b) (hma b)
      (fun i v hv => (Nat.cast_le.mpr (SimpleGraph.degree_le_of_le (hJF b))).trans (hdeg b i v hv))
  let prep (b : B) := Classical.choice (hp b)
  have hq (b : B) := prepared_quotient_cost (J b) (X b) (hXd b) (prep b) (W b)
    (hW b) (hXW b) n (D^(3/10:ℝ)) t ht (hn b) (hWnum b) ih
  choose k hk hkc using hq
  obtain ⟨K,hK,parts,used,hcount,hparts,hdis,hused,hFu,hpartscover⟩ :=
    hresolve D ((le_max_right _ _).trans hD) V A B G F P U hFG
      (fun r => (hPR r).trans (hRG r)) hPP hUU
      (fun r => (hFR r).mono_right (SimpleGraph.edgeSet_mono (hPR r))) hPe hr
      J W hJF hJJ hJu hW hWnum I X hXd hXW rX hXU hdeg prep k hk
  let : Fintype K := hK
  have husedR : used ⊆ ⋃ r, (R r).edgeSet := hused.trans (Set.iUnion_mono fun r => SimpleGraph.edgeSet_mono (hPR r))
  have hTu := protected_avoids_used R P T hRR hPR hTR (fun r => (hPT r).symm) used hused
  let H (r : A) := routerRemainder (R r) used
  have hcost := batch_remainder_ledger G F R hRG hRR hFR hcover parts hparts hdis used husedR hpartscover
  refine ⟨H,fun r => routerRemainder_le _ _,fun r => ?_,?_⟩
  · exact cutExpansionOn_mono (hTe r) (protected_le_remainder (hTR r) (hTu r))
  · have hkreal : (Fintype.card K:ℝ) ≤ (∑ b, (k b:ℝ)) + 8 * (∑ b, ∑ i, ((X b i).card:ℝ)) := by
      exact_mod_cast hcount
    have hqsum := Finset.sum_le_sum (s := univ) (fun b _ => hkc b)
    have hqsum' : (∑ b, (k b:ℝ)) ≤
        t * ((∑ b, ((W b).card:ℝ)) - ∑ b, ∑ i, ((X b i).card / 2:ℕ)) := by
      simpa only [Finset.mul_sum,Finset.sum_sub_distrib,mul_sub,Nat.cast_sum] using hqsum
    have hc : (decompositionCost G:ℝ) ≤ (Fintype.card K:ℝ) + ∑ r, (decompositionCost (H r):ℝ) := by
      exact_mod_cast hcost
    linarith

end
end ErdosGallai.Batch

end
end
end

end OAI
end

theorem solution : type_of% @OAI.ErdosGallai.Batch.uniform_coupled_resolution_cost_oai := @OAI.ErdosGallai.Batch.uniform_coupled_resolution_cost_oai
