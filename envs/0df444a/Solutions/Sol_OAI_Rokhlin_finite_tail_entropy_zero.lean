-- Prove2me | solution 1 for OAI.Rokhlin.finite_tail_entropy_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:59:36.77906+00:00
-- url     : https://prove2.me/submissions/cc1f5a7d-f8b0-4da0-9dec-abc9f9f263c9

import Mathlib
import Definitions.Def_Rokhlin
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Foundations
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Rokhlin

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

open MeasureTheory Filter
open scoped BigOperators Topology

section

section FiniteDistribution
variable {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
include hp hsum

theorem probability_le_one (a : A) : p a ≤ 1 := by
  rw [← hsum]
  exact Finset.single_le_sum (fun a _ => hp a) (Finset.mem_univ a)

theorem entropy_term_nonneg (a : A) : 0 ≤ -p a * Real.log (p a) := by
  rw [neg_mul, neg_nonneg]
  exact mul_nonpos_of_nonneg_of_nonpos (hp a)
    (Real.log_nonpos (hp a) (probability_le_one p hp hsum a))

theorem shannonEntropy_nonneg : 0 ≤ shannonEntropy p :=
  Finset.sum_nonneg (fun a _ => entropy_term_nonneg p hp hsum a)

end FiniteDistribution

end

section FactorEntropy
variable {A B : Type*} [Fintype A] [Fintype B]

theorem shannonEntropy_map_le [DecidableEq B] (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (f : A → B) :
    shannonEntropy (fun b => ∑ a, if f a = b then p a else 0) ≤ shannonEntropy p := by
  classical
  let q (b : B) := ∑ a, if f a = b then p a else 0
  have hpq (a : A) : p a ≤ q (f a) := by
    exact (by simpa [q] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun x => if f x = f a then p x else 0)
        (fun x _ => by split_ifs; exact hp x; exact le_rfl) (Finset.mem_univ a)))
  have he (b : B) : -q b * Real.log (q b) =
      ∑ a, if f a = b then -p a * Real.log (q b) else 0 := by
    change -(∑ a, if f a = b then p a else 0) * Real.log (q b) = _
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  change (∑ b, -q b * Real.log (q b)) ≤ ∑ a, -p a * Real.log (p a)
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonpos_left
      (Real.log_le_log ((hp a).lt_of_ne' ha) (hpq a)) (neg_nonpos.mpr (hp a))

end FactorEntropy
section
variable {Y A B : Type*} [MeasurableSpace Y] {η : Measure Y} [IsProbabilityMeasure η]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem randomEntropy_comp_le (F : Y → A) (hF : Measurable F) (g : A → B) :
    shannonEntropy (fun b => η.real ((g ∘ F) ⁻¹' {b})) ≤
      shannonEntropy (fun a => η.real (F ⁻¹' {a})) := by
  classical
  have he (b : B) : η.real ((g ∘ F) ⁻¹' {b}) =
      ∑ a, if g a = b then η.real (F ⁻¹' {a}) else 0 := by
    rw [← Finset.sum_filter]
    have hh := sum_measureReal_preimage_singleton (μ := η)
      (Finset.univ.filter (fun a => g a = b)) (fun a _ => hF (measurableSet_singleton a))
    rw [hh]
    congr 1
    ext y
    simp
  simp_rw [he]
  exact shannonEntropy_map_le _ (fun _ => measureReal_nonneg) g

end

open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate


open Filter
open scoped BigOperators Topology InnerProductSpace

open scoped BigOperators
open Polynomial

open scoped BigOperators

open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate


end Rokhlin

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Entropy
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

lemma shannonEntropy_eq_negMulLog (p : A → ℝ) :
    shannonEntropy p = ∑ a, Real.negMulLog (p a) := rfl

lemma rowEntropy_zero : rowEntropy (fun _ : A => 0) = 0 := by
  simp [rowEntropy,shannonEntropy,Real.negMulLog]

lemma zero_row {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (h : ∑ a, p a = 0) (a : A) : p a = 0 := by
  exact le_antisymm (h ▸ Finset.single_le_sum (fun a _ => hp a) (Finset.mem_univ a)) (hp a)

lemma rowEntropy_normalize (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
    rowEntropy p = (∑ a, p a) * shannonEntropy (fun a => p a / ∑ a, p a) := by
  classical
  let w := ∑ a, p a
  have hw : 0 ≤ w := Finset.sum_nonneg (fun a _ => hp a)
  by_cases hz : w = 0
  · have h0 : p = fun _ => 0 := funext (zero_row hp hz)
    subst p
    simp [rowEntropy_zero]
  · have hs : ∑ a, p a / w = 1 := by rw [←Finset.sum_div,div_self hz]
    have he (a : A) : Real.negMulLog (p a) =
        p a / w * Real.negMulLog w + w * Real.negMulLog (p a / w) := by
      conv_lhs => rw [show p a = w * (p a / w) by field_simp]
      exact Real.negMulLog_mul _ _
    simp only [rowEntropy,shannonEntropy_eq_negMulLog]
    change (∑ a, Real.negMulLog (p a)) - Real.negMulLog w = _
    simp_rw [he]
    rw [Finset.sum_add_distrib,←Finset.sum_mul,hs,one_mul,←Finset.mul_sum]
    ring

lemma rowEntropy_sum_le (p : B → A → ℝ) (hp : ∀ b a, 0 ≤ p b a) :
    (∑ b, rowEntropy (p b)) ≤ rowEntropy (fun a => ∑ b, p b a) := by
  classical
  let w (b : B) := ∑ a, p b a
  let s := ∑ b, w b
  have hw (b : B) : 0 ≤ w b := Finset.sum_nonneg (fun a _ => hp b a)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun b _ => hw b)
  by_cases hz : s = 0
  · have hw0 b : w b = 0 := zero_row hw hz b
    have hp0 b a : p b a = 0 := zero_row (hp b) (hw0 b) a
    have hpz : p = fun _ _ => 0 := funext fun b => funext (hp0 b)
    rw [hpz]
    simp only [Finset.sum_const_zero,rowEntropy_zero,le_refl]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hweights : ∑ b, w b / s = 1 := by rw [←Finset.sum_div,div_self hz]
    have he (a : A) : ∑ b, (w b / s) * (p b a / w b) = (∑ b, p b a) / s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hwb : w b = 0
      · rw [zero_row (hp b) hwb a,hwb]; simp
      · field_simp
    have hj (a : A) : ∑ b, (w b / s) * Real.negMulLog (p b a / w b) ≤
        Real.negMulLog ((∑ b, p b a) / s) := by
      have h := Real.concaveOn_negMulLog.le_map_sum
        (t := Finset.univ) (w := fun b => w b / s) (p := fun b => p b a / w b)
        (fun b _ => div_nonneg (hw b) hs) hweights
        (fun b _ => div_nonneg (hp b a) (hw b))
      simpa only [smul_eq_mul,he] using h
    rw [rowEntropy_normalize _ (fun a => Finset.sum_nonneg (fun b _ => hp b a))]
    have hsum : (∑ a, ∑ b, p b a) = s := Finset.sum_comm
    rw [hsum]
    calc
      ∑ b, rowEntropy (p b) = s * ∑ a, ∑ b, (w b / s) * Real.negMulLog (p b a / w b) := by
        simp_rw [rowEntropy_normalize _ (hp _),shannonEntropy_eq_negMulLog]
        rw [Finset.sum_comm,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [←Finset.mul_sum,←mul_assoc,mul_div_cancel₀ _ hz]
      _ ≤ s * ∑ a, Real.negMulLog ((∑ b, p b a) / s) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hj a)) hs
      _ = _ := rfl

lemma shannon_chain_rule (p : B → A → ℝ) :
    shannonEntropy (fun z : B × A => p z.1 z.2) =
      shannonEntropy (fun b => ∑ a, p b a) + conditionalShannon p := by
  simp only [conditionalShannon,rowEntropy,shannonEntropy_eq_negMulLog,Fintype.sum_prod_type,
    Finset.sum_sub_distrib]
  ring

lemma conditionalShannon_refine (p : C → B → A → ℝ) (hp : ∀ c b a, 0 ≤ p c b a) :
    conditionalShannon (fun z : C × B => p z.1 z.2) ≤
      conditionalShannon (fun b a => ∑ c, p c b a) := by
  simp only [conditionalShannon,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun b _ => rowEntropy_sum_le (fun c a => p c b a) (fun c a => hp c b a)
end

section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω A B C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]

omit [Fintype B] in
lemma sum_joint_mass (F : Ω → A) (G : Ω → B) (hF : Measurable F) (hG : Measurable G) (b : B) :
    (∑ a, μ.real {x | G x = b ∧ F x = a}) = μ.real (G ⁻¹' {b}) := by
  rw [←measureReal_iUnion_fintype]
  · congr 1
    ext x
    simp
  · intro a a' haa
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact haa (hx.2.symm.trans hx'.2)
  · intro a
    exact (hG (measurableSet_singleton b)).inter (hF (measurableSet_singleton a))

lemma randomEntropy_pair (F : Ω → A) (G : Ω → B) (hF : Measurable F) (hG : Measurable G) :
    randomEntropy μ (fun x => (G x,F x)) = randomEntropy μ G + randomConditionalEntropy μ F G := by
  have h := shannon_chain_rule (fun b a => μ.real {x | G x = b ∧ F x = a})
  simp_rw [sum_joint_mass μ F G hF hG] at h
  simpa only [randomEntropy,randomConditionalEntropy,Set.preimage,Set.mem_singleton_iff,Prod.ext_iff] using h

lemma randomEntropy_nonneg (F : Ω → A) (hF : Measurable F) : 0 ≤ randomEntropy μ F := by
  apply shannonEntropy_nonneg _ (fun _ => measureReal_nonneg)
  simpa using (sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (fun a _ => hF (measurableSet_singleton a)))

lemma randomConditionalEntropy_nonneg (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) : 0 ≤ randomConditionalEntropy μ F G := by
  have h := randomEntropy_comp_le (η := μ) (fun x => (G x,F x)) (hG.prodMk hF) Prod.fst
  change randomEntropy μ G ≤ randomEntropy μ (fun x => (G x,F x)) at h
  rw [randomEntropy_pair μ F G hF hG] at h
  linarith

lemma randomConditionalEntropy_le (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) : randomConditionalEntropy μ F G ≤ randomEntropy μ F := by
  have h := rowEntropy_sum_le (fun b a => μ.real {x | G x = b ∧ F x = a})
    (fun _ _ => measureReal_nonneg)
  have hsum (a : A) : (∑ b, μ.real {x | G x = b ∧ F x = a}) = μ.real (F ⁻¹' {a}) := by
    have hh := sum_joint_mass μ G F hG hF a
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ext x
    exact and_comm
  simp_rw [hsum] at h
  have hmass : (∑ a, μ.real (F ⁻¹' {a})) = 1 := by
    simpa using (sum_measureReal_preimage_singleton (μ := μ) Finset.univ
      (fun a _ => hF (measurableSet_singleton a)))
  simpa only [randomConditionalEntropy,conditionalShannon, rowEntropy,hmass,Real.negMulLog_one,
    sub_zero,randomEntropy] using h

lemma randomConditionalEntropy_refine (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K) :
    randomConditionalEntropy μ F (fun x => (K x,G x)) ≤ randomConditionalEntropy μ F G := by
  have hp := conditionalShannon_refine
    (fun c b a => μ.real {x | K x = c ∧ G x = b ∧ F x = a}) (fun _ _ _ => measureReal_nonneg)
  have he (b : B) (a : A) : (∑ c, μ.real {x | K x = c ∧ G x = b ∧ F x = a}) =
      μ.real {x | G x = b ∧ F x = a} := by
    have hh := sum_joint_mass μ K (fun x => (G x,F x)) hK (hG.prodMk hF) (b,a)
    simpa only [Set.preimage,Set.mem_singleton_iff,Prod.mk.injEq,and_comm,and_left_comm] using hh
  simp_rw [he] at hp
  simpa only [randomConditionalEntropy,Prod.ext_iff,and_assoc] using hp

end

section
open MeasureTheory Filter
open scoped Topology BigOperators symmDiff
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma continuous_shannonEntropy : Continuous (shannonEntropy (A := A)) := by
  unfold shannonEntropy
  exact continuous_finsetSum _ fun a _ => Real.continuous_negMulLog.comp (continuous_apply a)

omit [IsProbabilityMeasure μ] in
lemma randomEntropy_measurePreserving {Υ : Type*} [MeasurableSpace Υ] (ν : Measure Υ)
    [IsProbabilityMeasure ν] {T : Ω → Υ} (hT : MeasurePreserving T μ ν)
    (F : Υ → A) (hF : Measurable F) : randomEntropy μ (F ∘ T) = randomEntropy ν F := by
  unfold randomEntropy
  congr 1
  funext a
  exact hT.measureReal_preimage (hF (measurableSet_singleton a)).nullMeasurableSet

omit [Fintype A] in
lemma atom_mass_disagreement {F G : Ω → A} (hF : Measurable F) (hG : Measurable G) (a : A) :
    |μ.real (F ⁻¹' {a}) - μ.real (G ⁻¹' {a})| ≤ μ.real {x | F x ≠ G x} := by
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hF (measurableSet_singleton a)).nullMeasurableSet
    (hG (measurableSet_singleton a)).nullMeasurableSet).trans
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  simp only [Set.mem_symmDiff,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq] at hx ⊢
  rcases hx with hx | hx <;> aesop

lemma randomEntropy_tendsto_of_disagreement {ι : Type*} {l : Filter ι} {Fn : ι → Ω → A} {F : Ω → A}
    (hFn : ∀ n, Measurable (Fn n)) (hF : Measurable F)
    (h : Tendsto (fun n => μ.real {x | Fn n x ≠ F x}) l (𝓝 0)) :
    Tendsto (fun n => randomEntropy μ (Fn n)) l (𝓝 (randomEntropy μ F)) := by
  apply continuous_shannonEntropy.tendsto _ |>.comp
  apply tendsto_pi_nhds.mpr
  intro a
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs,abs_abs] using atom_mass_disagreement μ (hFn n) hF a) h

lemma randomEntropy_self_pair (F : Ω → A) (hF : Measurable F) :
    randomEntropy μ (fun x => (F x,F x)) = randomEntropy μ F := by
  apply le_antisymm (randomEntropy_comp_le F hF (fun a => (a,a)))
  have h := randomEntropy_comp_le (η := μ) (fun x => (F x,F x)) (hF.prodMk hF) Prod.fst
  exact h

lemma randomConditionalEntropy_tendsto_self {ι : Type*} {l : Filter ι} {Fn : ι → Ω → A} {F : Ω → A}
    (hFn : ∀ n, Measurable (Fn n)) (hF : Measurable F)
    (h : Tendsto (fun n => μ.real {x | Fn n x ≠ F x}) l (𝓝 0)) :
    Tendsto (fun n => randomConditionalEntropy μ F (Fn n)) l (𝓝 0) := by
  have hp : Tendsto (fun n => μ.real {x | (Fn n x,F x) ≠ (F x,F x)}) l (𝓝 0) := by
    have he : (fun n => μ.real {x | (Fn n x,F x) ≠ (F x,F x)}) =
        (fun n => μ.real {x | Fn n x ≠ F x}) := by
      funext n
      congr 1
      ext x
      constructor
      · intro hn he
        exact hn (congrArg (fun a => (a,F x)) he)
      · intro hn he
        exact hn (congrArg Prod.fst he)
    rwa [he]
  have ht := (randomEntropy_tendsto_of_disagreement μ (fun n => (hFn n).prodMk hF)
    (hF.prodMk hF) hp).sub (randomEntropy_tendsto_of_disagreement μ hFn hF h)
  have he n : randomEntropy μ (fun x => (Fn n x,F x)) - randomEntropy μ (Fn n) =
      randomConditionalEntropy μ F (Fn n) := by rw [randomEntropy_pair μ F (Fn n) hF (hFn n)]; ring
  simpa only [he,randomEntropy_self_pair μ F hF,sub_self] using ht
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B C D : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [retained0 : IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [retained1 : MeasurableSpace A] [retained2 : MeasurableSingletonClass A]
    [retained3 : MeasurableSpace B] [retained4 : MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [MeasurableSingletonClass D]

lemma randomEntropy_mutual_factor (F : Ω → A) (G : Ω → B) (hF : Measurable F) (hG : Measurable G)
    (e : A → B) (r : B → A) (he : G = e ∘ F) (hr : F = r ∘ G) :
    randomEntropy μ F = randomEntropy μ G := by
  apply le_antisymm
  · rw [hr]
    exact randomEntropy_comp_le G hG r
  · rw [he]
    exact randomEntropy_comp_le F hF e

lemma randomEntropy_pair_factor (F : Ω → A) (hF : Measurable F) (e : A → B) :
    randomEntropy μ (fun x => (F x,e (F x))) = randomEntropy μ F := by
  apply randomEntropy_mutual_factor μ _ F (hF.prodMk ((measurable_of_finite e).comp hF)) hF
    Prod.fst (fun a => (a,e a)) rfl rfl

lemma randomConditionalEntropy_condition_redundant (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) (e : B → C) :
    randomConditionalEntropy μ F (fun x => (G x,e (G x))) = randomConditionalEntropy μ F G := by
  have hp := randomEntropy_pair μ F (fun x => (G x,e (G x))) hF
    (hG.prodMk ((measurable_of_finite e).comp hG))
  have hq := randomEntropy_pair μ F G hF hG
  have hj : randomEntropy μ (fun x => ((G x,e (G x)),F x)) =
      randomEntropy μ (fun x => (G x,F x)) := by
    exact randomEntropy_mutual_factor μ _ _
      ((hG.prodMk ((measurable_of_finite e).comp hG)).prodMk hF) (hG.prodMk hF)
      (fun z => (z.1.1,z.2)) (fun z => ((z.1,e z.1),z.2)) rfl rfl
  rw [hj,randomEntropy_pair_factor μ G hG e] at hp
  linarith

lemma randomConditionalEntropy_condition_comp (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) (e : B → C) :
    randomConditionalEntropy μ F G ≤ randomConditionalEntropy μ F (e ∘ G) := by
  have h := randomConditionalEntropy_refine μ F (e ∘ G) G hF
    ((measurable_of_finite e).comp hG) hG
  change randomConditionalEntropy μ F (fun x => (G x,e (G x))) ≤ _ at h
  rwa [randomConditionalEntropy_condition_redundant μ F G hF hG e] at h

lemma randomConditionalEntropy_measurable_factor (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hK : Measurable K) [Nonempty B]
    (hG : Measurable[MeasurableSpace.comap K inferInstance] G) :
    randomConditionalEntropy μ F K ≤ randomConditionalEntropy μ F G := by
  obtain ⟨e,he⟩ := (Function.factorsThrough_iff G).mp hG.factorsThrough
  rw [he]
  exact randomConditionalEntropy_condition_comp μ F K hF hK e

lemma randomConditionalEntropy_measurePreserving {Υ : Type*} [MeasurableSpace Υ] (ν : Measure Υ)
    [IsProbabilityMeasure ν] {T : Ω → Υ} (hT : MeasurePreserving T μ ν)
    (F : Υ → A) (G : Υ → B) (hF : Measurable F) (hG : Measurable G) :
    randomConditionalEntropy μ (F ∘ T) (G ∘ T) = randomConditionalEntropy ν F G := by
  have h := randomEntropy_pair μ (F ∘ T) (G ∘ T) (hF.comp hT.measurable) (hG.comp hT.measurable)
  have h' := randomEntropy_pair ν F G hF hG
  have hp := randomEntropy_measurePreserving μ ν hT (fun x => (G x,F x)) (hG.prodMk hF)
  have hg := randomEntropy_measurePreserving μ ν hT G hG
  change randomEntropy μ (fun x => ((G ∘ T) x,(F ∘ T) x)) = _ at hp
  rw [hp,hg] at h
  linarith

end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]

lemma randomConditionalEntropy_chain (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K) :
    randomConditionalEntropy μ (fun x => (G x,F x)) K =
      randomConditionalEntropy μ G K + randomConditionalEntropy μ F (fun x => (K x,G x)) := by
  have h1 := randomEntropy_pair μ (fun x => (G x,F x)) K (hG.prodMk hF) hK
  have h2 := randomEntropy_pair μ F (fun x => (K x,G x)) hF (hK.prodMk hG)
  have h3 := randomEntropy_pair μ G K hG hK
  have he : randomEntropy μ (fun x => (K x,(G x,F x))) =
      randomEntropy μ (fun x => ((K x,G x),F x)) := by
    exact randomEntropy_mutual_factor μ _ _ (hK.prodMk (hG.prodMk hF)) ((hK.prodMk hG).prodMk hF)
      (fun z => ((z.1,z.2.1),z.2.2)) (fun z => (z.1.1,(z.1.2,z.2))) rfl rfl
  linarith

lemma randomConditionalEntropy_mutual_factor (F : Ω → A) (G : Ω → B) (K : Ω → C)
    (hF : Measurable F) (hG : Measurable G) (hK : Measurable K)
    (e : A → B) (r : B → A) (he : G = e ∘ F) (hr : F = r ∘ G) :
    randomConditionalEntropy μ F K = randomConditionalEntropy μ G K := by
  have h1 := randomEntropy_pair μ F K hF hK
  have h2 := randomEntropy_pair μ G K hG hK
  have he' : (fun x => (K x,G x)) = (fun z : C × A => (z.1,e z.2)) ∘ (fun x => (K x,F x)) := by rw [he]; rfl
  have hr' : (fun x => (K x,F x)) = (fun z : C × B => (z.1,r z.2)) ∘ (fun x => (K x,G x)) := by rw [hr]; rfl
  have h := randomEntropy_mutual_factor μ _ _ (hK.prodMk hF) (hK.prodMk hG)
    (fun z : C × A => (z.1,e z.2)) (fun z : C × B => (z.1,r z.2)) he' hr'
  linarith

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma randomEntropy_fintype_one [Unique A] (F : Ω → A) : randomEntropy μ F = 0 := by
  classical
  have he : F = fun _ => default := funext fun x => Unique.eq_default _
  rw [he]
  simp [randomEntropy,shannonEntropy]

lemma randomConditionalEntropy_fintype_one [Unique A] (F : Ω → A) (G : Ω → B)
    (hF : Measurable F) (hG : Measurable G) : randomConditionalEntropy μ F G = 0 := by
  apply le_antisymm _ (randomConditionalEntropy_nonneg μ F G hF hG)
  have h := randomConditionalEntropy_le μ F G hF hG
  rwa [randomEntropy_fintype_one μ F] at h

omit [Fintype A] [MeasurableSingletonClass A] in
lemma measurable_integerWord (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (n : ℕ) :
    Measurable (integerWord F t n) := Measurable.of_eval fun _ => hF _

lemma integerWord_pair (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (m n : ℕ) :
    randomEntropy μ (integerWord F t (m+n)) =
      randomEntropy μ (fun x => (integerWord F t m x,integerWord F (t+m) n x)) := by
  apply randomEntropy_mutual_factor μ _ _ (measurable_integerWord F hF _ _)
    ((measurable_integerWord F hF _ _).prodMk (measurable_integerWord F hF _ _))
    (fun z => (fun i => z (i.castAdd n),fun i => z (i.natAdd m)))
    (fun z => Fin.append z.1 z.2)
  · funext x
    apply Prod.ext
    · rfl
    · funext i
      simp only [integerWord,Function.comp_apply,Fin.val_natAdd,Nat.cast_add]
      congr 1
      ring
  · funext x i
    induction i using Fin.addCases with
    | left i => simp [integerWord]
    | right i => simp only [integerWord,Function.comp_apply,Fin.append_right,Fin.val_natAdd,Nat.cast_add]; congr 1; ring

lemma integerWord_add (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (m n : ℕ) :
    randomEntropy μ (integerWord F t (m+n)) = randomEntropy μ (integerWord F t m) +
      randomConditionalEntropy μ (integerWord F (t+m) n) (integerWord F t m) := by
  rw [integerWord_pair μ F hF t m n,randomEntropy_pair μ _ _
    (measurable_integerWord F hF _ _) (measurable_integerWord F hF _ _)]

lemma integerWord_succ (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (n : ℕ) :
    randomEntropy μ (integerWord F t (n+1)) = randomEntropy μ (integerWord F t n) +
      randomConditionalEntropy μ (F (t+n)) (integerWord F t n) := by
  rw [integerWord_add μ F hF t n 1]
  congr 1
  apply randomConditionalEntropy_mutual_factor μ _ _ _ (measurable_integerWord F hF _ _)
    (hF _) (measurable_integerWord F hF _ _) (fun z => z 0) (fun a _ => a)
  · funext x
    simp [integerWord]
  · funext x i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [integerWord,Fin.val_zero,Nat.cast_zero,add_zero,Function.comp_apply]

end

section
open Filter
open scoped Topology BigOperators

theorem entropy_rate_of_decreasing_increments (H : ℕ → ℝ) (h0 : H 0 = 0)
    (hmono : Antitone (fun n => H (n+1) - H n))
    (hpos : ∀ n, 0 ≤ H (n+1) - H n) :
    ∃ h : ℝ, 0 ≤ h ∧ (∀ n, h ≤ H (n+1) - H n) ∧
      Tendsto (fun n : ℕ => H n / n) atTop (𝓝 h) := by
  let a : ℕ → ℝ := fun n => H (n+1) - H n
  have hb : BddBelow (Set.range a) := ⟨0,by rintro _ ⟨n,rfl⟩; exact hpos n⟩
  refine ⟨⨅ n, a n,?_,fun n => ciInf_le hb n,?_⟩
  · exact le_ciInf (fun n => hpos n)
  · have ht := (tendsto_atTop_ciInf hmono hb).cesaro
    have he n : (∑ j ∈ Finset.range n, a j) = H n := by
      dsimp [a]
      rw [Finset.sum_range_sub,h0,sub_zero]
    simpa only [a,Finset.sum_range_sub,h0,sub_zero,div_eq_mul_inv,mul_comm] using ht

theorem entropy_zero_of_tail_bounds (H K : ℕ → ℝ) (h : ℝ)
    (hrate : Tendsto (fun n : ℕ => H n / n) atTop (𝓝 h))
    (hK : ∀ n, 0 ≤ K n)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ c : ℕ, ∀ n : ℕ,
      K n + n * h ≤ H (n+c) + n * ε) :
    Tendsto (fun n : ℕ => K n / n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (div_nonneg (hK n) (Nat.cast_nonneg n))
  · intro ε hε
    obtain ⟨c,hc⟩ := hb (ε/2) (by positivity)
    have hd : Tendsto (fun n : ℕ => (n+c : ℝ) / n) atTop (𝓝 1) := by
      have ht : Tendsto (fun n : ℕ => (c:ℝ) / n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
      have hh : Tendsto (fun n : ℕ => 1 + c / (n : ℝ)) atTop (𝓝 (1+0)) := tendsto_const_nhds.add ht
      simp only [add_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp
    have hsh : Tendsto (fun n : ℕ => H (n+c) / n) atTop (𝓝 h) := by
      have hh := (hrate.comp (tendsto_add_atTop_nat c)).mul hd
      rw [mul_one] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n+c : ℝ) ≠ 0 := by positivity
      simp only [Function.comp_def,Nat.cast_add]
      field_simp
    have hu := (hsh.sub_const h).add_const (ε/2)
    simp only [sub_self,zero_add] at hu
    filter_upwards [hu.eventually (gt_mem_nhds (show ε/2 < ε by linarith)),
      eventually_ge_atTop 1] with n hh hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    apply lt_of_le_of_lt _ hh
    apply (div_le_iff₀ hn').mpr
    have hf := hc n
    have he : (H (n+c) / n - h + ε/2) * n = H (n+c) - n*h + n*(ε/2) := by
      field_simp
    rw [he]
    linarith
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A : Type*} [retained5 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MeasurableSpace Ω] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma integerWord_subword (F : ℤ → Ω → A) (s : ℤ) (l n m : ℕ) (h : l+n ≤ m) :
    integerWord F (s+l) n = (fun z : Fin m → A => fun i : Fin n =>
      z ⟨l+i.val,by omega⟩) ∘ integerWord F s m := by
  funext x i
  simp only [integerWord,Function.comp_apply,Nat.cast_add]
  congr 1
  ring

omit [MeasurableSpace Ω] in
lemma integerWord_subword_measurable (F : ℤ → Ω → A) (s : ℤ) (l n m : ℕ) (h : l+n ≤ m) :
    Measurable[MeasurableSpace.comap (integerWord F s m) inferInstance] (integerWord F (s+l) n) := by
  rw [integerWord_subword F s l n m h]
  exact (measurable_of_finite _).comp (comap_measurable _)

include retained5 in
lemma pastWord_comap_mono (F : ℤ → Ω → A) (t : ℤ) :
    Monotone (fun n : ℕ => MeasurableSpace.comap (integerWord F (t-n) n) inferInstance) := by
  let _ := retained5
  intro m n hmn
  have hh := integerWord_subword_measurable F (t-n) (n-m) m n (by omega)
  have he : t - (n:ℤ) + (n-m:ℕ) = t-m := by rw [Nat.cast_sub hmn]; ring
  rw [he] at hh
  exact hh.comap_le

include retained5 in
lemma windowWord_comap_mono (F : ℤ → Ω → A) :
    Monotone (fun n : ℕ => MeasurableSpace.comap (integerWord F (-(n:ℤ)) (2*n+1)) inferInstance) := by
  let _ := retained5
  intro m n hmn
  have hh := integerWord_subword_measurable F (-(n:ℤ)) (n-m) (2*m+1) (2*n+1) (by omega)
  have he : -(n:ℤ) + (n-m:ℕ) = -(m:ℤ) := by rw [Nat.cast_sub hmn]; ring
  rw [he] at hh
  exact hh.comap_le

variable (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (htrans : ∀ t s x, F (t+s) x = F t (U s x))

omit [MeasurableSpace Ω] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
include htrans in
lemma integerWord_translate (t s : ℤ) (n : ℕ) :
    integerWord F (t+s) n = integerWord F t n ∘ U s := by
  funext x i
  change F ((t+s)+i.val) x = F (t+i.val) (U s x)
  rw [show (t+s)+(i.val:ℤ) = (t+i.val)+s by ring,htrans]

include hU hF htrans
lemma integerWord_entropy_translate (t : ℤ) (n : ℕ) :
    randomEntropy μ (integerWord F t n) = randomEntropy μ (integerWord F 0 n) := by
  rw [show t = 0+t by simp,integerWord_translate U F htrans]
  exact randomEntropy_measurePreserving μ μ (hU t) _ (measurable_integerWord F hF _ _)

lemma conditionalEntropy_past_translate (t : ℤ) (n : ℕ) :
    randomConditionalEntropy μ (F t) (integerWord F (t-n) n) =
      randomConditionalEntropy μ (F 0) (integerWord F (-(n:ℤ)) n) := by
  have he : integerWord F (t-n) n = integerWord F (-(n:ℤ)) n ∘ U t := by
    rw [show t - (n:ℤ) = -(n:ℤ)+t by ring,integerWord_translate U F htrans]
  have hf : F t = F 0 ∘ U t := by funext x; simpa using htrans 0 t x
  rw [he,hf]
  exact randomConditionalEntropy_measurePreserving μ μ (hU t) _ _ (hF _) (measurable_integerWord F hF _ _)

lemma entropy_increment_past (n : ℕ) :
    randomEntropy μ (integerWord F 0 (n+1)) - randomEntropy μ (integerWord F 0 n) =
      randomConditionalEntropy μ (F 0) (integerWord F (-(n:ℤ)) n) := by
  have hh := integerWord_succ μ F hF (-(n:ℤ)) n
  rw [integerWord_entropy_translate μ U hU F hF htrans (-(n:ℤ)) (n+1),
    integerWord_entropy_translate μ U hU F hF htrans (-(n:ℤ)) n] at hh
  simp only [neg_add_cancel] at hh
  linarith

theorem stationary_entropy_rate [Nonempty A] :
    ∃ h : ℝ, 0 ≤ h ∧
      (∀ (t : ℤ) (n : ℕ), h ≤ randomConditionalEntropy μ (F t) (integerWord F (t-n) n)) ∧
      Tendsto (fun n : ℕ => randomEntropy μ (integerWord F 0 n) / n) atTop (𝓝 h) := by
  let H : ℕ → ℝ := fun n => randomEntropy μ (integerWord F 0 n)
  have h0 : H 0 = 0 := randomEntropy_fintype_one μ _
  have he n : H (n+1) - H n = randomConditionalEntropy μ (F 0) (integerWord F (-(n:ℤ)) n) :=
    entropy_increment_past μ U hU F hF htrans n
  have hmono : Antitone (fun n => H (n+1) - H n) := by
    intro m n hmn
    change H (n+1) - H n ≤ H (m+1) - H m
    rw [he,he]
    apply randomConditionalEntropy_measurable_factor μ _ _ _ (hF 0) (measurable_integerWord F hF _ _)
    have hh := (pastWord_comap_mono F 0 hmn)
    simp only [zero_sub] at hh
    exact (comap_measurable _).mono hh le_rfl
  have hpos n : 0 ≤ H (n+1)-H n := by
    rw [he]
    exact randomConditionalEntropy_nonneg μ _ _ (hF _) (measurable_integerWord F hF _ _)
  obtain ⟨h,hpos,hle,ht⟩ := entropy_rate_of_decreasing_increments H h0 hmono hpos
  refine ⟨h,hpos,?_,ht⟩
  intro t n
  rw [conditionalEntropy_past_translate μ U hU F hF htrans,←he]
  exact hle n
end

section
open MeasureTheory Filter Set
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma le_completedFactor {m : MeasurableSpace Ω} (hm : m ≤ m₀) : m ≤ completedFactor (m₀ := m₀) μ m :=
  fun s hs => ⟨hm s hs,s,hs,Eventually.of_forall fun _ => Iff.rfl⟩

lemma completedFactor_mono : Monotone (completedFactor (m₀ := m₀) μ) := by
  intro m n h s hs
  obtain ⟨hs,t,ht,he⟩ := hs
  exact ⟨hs,t,h t ht,he⟩

end

section
open MeasureTheory Filter Set
open scoped Topology BigOperators symmDiff
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma set_approx_iSup_completed (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hmono : Monotone m) {s : Set Ω}
    (hs : MeasurableSet[completedFactor (m₀ := m₀) μ (⨆ n, m n)] s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n t, MeasurableSet[m n] t ∧ μ.real (s ∆ t) < ε := by
  have hle : (⨆ n, m n) ≤ m₀ := iSup_le hm
  let C : Set (Set Ω) := {t | ∃ n, MeasurableSet[m n] t}
  have hCalg : IsSetAlgebra C := by
    refine ⟨⟨0,@MeasurableSet.empty Ω (m 0)⟩,?_,?_⟩
    · rintro t ⟨n,hn⟩
      exact ⟨n,hn.compl⟩
    · rintro t t' ⟨n,hn⟩ ⟨k,hk⟩
      exact ⟨max n k,((hmono (le_max_left n k)) _ hn).union ((hmono (le_max_right n k)) _ hk)⟩
  have hCgen : (⨆ n, m n) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · apply iSup_le
      intro n t ht
      exact MeasurableSpace.measurableSet_generateFrom ⟨n,ht⟩
    · apply MeasurableSpace.generateFrom_le
      rintro t ⟨n,hn⟩
      exact (le_iSup m n) _ hn
  have hdense := @Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite Ω (⨆ n, m n) (μ.trim hle)
    C inferInstance hCalg hCgen
  obtain ⟨t,ht,he⟩ := hs.2
  obtain ⟨r,⟨n,hn⟩,hr⟩ := @Measure.MeasureDense.approx Ω (⨆ n, m n) (μ.trim hle) C hdense t ht (by finiteness) ε hε
  have hrAll : MeasurableSet[(⨆ n, m n)] r := (le_iSup m n) _ hn
  rw [trim_measurableSet_eq hle (ht.symmDiff hrAll)] at hr
  have he' : s ∆ r =ᵐ[μ] t ∆ r := by
    filter_upwards [he] with x hx
    apply propext
    change x ∈ s ∆ r ↔ x ∈ t ∆ r
    simp only [Set.mem_symmDiff,hx]
  refine ⟨n,r,hn,?_⟩
  have her : μ.real (s ∆ r) = μ.real (t ∆ r) := measureReal_congr he'
  apply lt_of_eq_of_lt her
  have hh := ENNReal.toReal_lt_toReal (measure_ne_top μ (t ∆ r)) ENNReal.ofReal_ne_top |>.mpr hr
  simpa only [Measure.real,ENNReal.toReal_ofReal hε.le] using hh

variable {B : Type*} [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [MeasurableSpace B] [MeasurableSingletonClass B] in
lemma pickFiniteBit_eq (b : B) (v : B → Bool) (hv : ∀ a, v a = true ↔ a = b) :
    pickFiniteBit v = b := by
  have he : ∃ a, v a = true := ⟨b,(hv b).mpr rfl⟩
  simp only [pickFiniteBit,dite_eq_left he]
  exact (hv _).mp (Classical.choose_spec he)

lemma finite_approx_iSup_completed (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hmono : Monotone m) (F : Ω → B)
    (hF : Measurable[completedFactor (m₀ := m₀) μ (⨆ n, m n)] F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n G, Measurable[m n] G ∧ μ.real {x | G x ≠ F x} < ε := by
  classical
  let δ := ε / (Fintype.card B + 1 : ℝ)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsets (b : B) := set_approx_iSup_completed μ m hm hmono
    (hF (measurableSet_singleton b)) δ hδ
  choose n r hr hεr using hsets
  let N := Finset.univ.sup n
  have hrN (b : B) : MeasurableSet[m N] (r b) :=
    (hmono (Finset.le_sup (f := n) (Finset.mem_univ b))) _ (hr b)
  let code : Ω → B → Bool := fun x b => if x ∈ r b then true else false
  have hcode : Measurable[m N] code := by
    refine @Measurable.of_eval Ω B (fun _ => Bool) (m N) _ code ?_
    intro b
    exact Measurable.ite (hrN b) measurable_const measurable_const
  let G : Ω → B := pickFiniteBit ∘ code
  have hG : Measurable[m N] G := (measurable_of_finite pickFiniteBit).comp hcode
  have hsub : {x | G x ≠ F x} ⊆ ⋃ b, ((F ⁻¹' {b}) ∆ r b) := by
    intro x hx
    by_contra hn
    have hbits (b : B) : code x b = true ↔ b = F x := by
      have hh : x ∉ (F ⁻¹' {b}) ∆ r b := fun hh => hn (Set.mem_iUnion.mpr ⟨b,hh⟩)
      simp only [Set.mem_symmDiff,Set.mem_preimage,Set.mem_singleton_iff,not_or] at hh
      simp only [code,ite_eq_left_iff,Bool.false_eq_true,imp_false]
      aesop
    exact hx (pickFiniteBit_eq (F x) (code x) hbits)
  refine ⟨N,G,hG,lt_of_le_of_lt ((measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)) ?_⟩
  calc
    (∑ b, μ.real ((F ⁻¹' {b}) ∆ r b)) ≤ ∑ _ : B, δ := Finset.sum_le_sum fun b _ => (hεr b).le
    _ = (Fintype.card B : ℝ) * δ := by simp
    _ < ε := by
      have hd : (0 : ℝ) < Fintype.card B + 1 := by positivity
      dsimp [δ]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hd).mpr (by nlinarith)
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

lemma randomConditionalEntropy_tendsto_condition {ι : Type*} {l : Filter ι}
    (F : Ω → A) (hF : Measurable F) {Gn : ι → Ω → B} {G : Ω → B}
    (hGn : ∀ n, Measurable (Gn n)) (hG : Measurable G)
    (h : Tendsto (fun n => μ.real {x | Gn n x ≠ G x}) l (𝓝 0)) :
    Tendsto (fun n => randomConditionalEntropy μ F (Gn n)) l (𝓝 (randomConditionalEntropy μ F G)) := by
  have hp : Tendsto (fun n => μ.real {x | (Gn n x,F x) ≠ (G x,F x)}) l (𝓝 0) := by
    have he : (fun n => μ.real {x | (Gn n x,F x) ≠ (G x,F x)}) =
        (fun n => μ.real {x | Gn n x ≠ G x}) := by
      funext n
      congr 1
      ext x
      constructor
      · intro hn he
        exact hn (congrArg (fun a => (a,F x)) he)
      · intro hn he
        exact hn (congrArg Prod.fst he)
    rwa [he]
  have ht := (randomEntropy_tendsto_of_disagreement μ (fun n => (hGn n).prodMk hF)
    (hG.prodMk hF) hp).sub (randomEntropy_tendsto_of_disagreement μ hGn hG h)
  have he (H : Ω → B) (hH : Measurable H) : randomEntropy μ (fun x => (H x,F x)) - randomEntropy μ H =
      randomConditionalEntropy μ F H := by rw [randomEntropy_pair μ F H hF hH]; ring
  simpa only [he G hG,he _ (hGn _)] using ht

lemma finite_approx_completed_sequence [Nonempty B]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀) (hmono : Monotone m)
    (G : Ω → B) (hG : Measurable[completedFactor (m₀ := m₀) μ (⨆ n, m n)] G) :
    ∃ n : ℕ → ℕ, ∃ Gn : ℕ → Ω → B, (∀ l, Measurable[m (n l)] (Gn l)) ∧
      Tendsto (fun l => μ.real {x | Gn l x ≠ G x}) atTop (𝓝 0) := by
  have hs (l : ℕ) := finite_approx_iSup_completed μ m hm hmono G hG (1 / (l+1 : ℝ)) (by positivity)
  choose n Gn hGn he using hs
  refine ⟨n,Gn,hGn,?_⟩
  have ht : Tendsto (fun l : ℕ => 1 / (l+1 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  exact squeeze_zero (fun _ => measureReal_nonneg) (fun l => (he l).le) ht

lemma exists_conditional_entropy_lt_of_completed [Nonempty A]
    {C : ℕ → Type*} [∀ n, Fintype (C n)] [∀ n, MeasurableSpace (C n)]
    [∀ n, MeasurableSingletonClass (C n)] (K : ∀ n, Ω → C n)
    (hK : ∀ n, Measurable (K n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (K n) inferInstance))
    (F : Ω → A) (hF : Measurable[completedFactor (m₀ := m₀) μ
      (⨆ n, MeasurableSpace.comap (K n) inferInstance)] F)
    (ε : ℝ) (hε : 0 < ε) : ∃ n, randomConditionalEntropy μ F (K n) < ε := by
  have hm n : MeasurableSpace.comap (K n) inferInstance ≤ m₀ := (hK n).comap_le
  obtain ⟨n,G,hG,ht⟩ := finite_approx_completed_sequence μ _ hm hmono F hF
  have hF0 : Measurable F := hF.mono (completedFactor_le μ _) le_rfl
  have hG0 l : Measurable (G l) := (hG l).mono (hm _) le_rfl
  have hcond := randomConditionalEntropy_tendsto_self μ hG0 hF0 ht
  obtain ⟨l,hl⟩ := (hcond.eventually (gt_mem_nhds hε)).exists
  refine ⟨n l,lt_of_le_of_lt ?_ hl⟩
  exact randomConditionalEntropy_measurable_factor μ F (G l) (K (n l)) hF0 (hK _) (hG l)

lemma conditional_entropy_lower_of_completed [Nonempty B]
    {C : ℕ → Type*} [∀ n, Fintype (C n)] [∀ n, MeasurableSpace (C n)]
    [∀ n, MeasurableSingletonClass (C n)] (K : ∀ n, Ω → C n)
    (hK : ∀ n, Measurable (K n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (K n) inferInstance))
    (F : Ω → A) (hF : Measurable F) (G : Ω → B)
    (hG : Measurable[completedFactor (m₀ := m₀) μ
      (⨆ n, MeasurableSpace.comap (K n) inferInstance)] G)
    (r : ℝ) (hr : ∀ n, r ≤ randomConditionalEntropy μ F (K n)) :
    r ≤ randomConditionalEntropy μ F G := by
  have hm n : MeasurableSpace.comap (K n) inferInstance ≤ m₀ := (hK n).comap_le
  obtain ⟨n,Gn,hGn,ht⟩ := finite_approx_completed_sequence μ _ hm hmono G hG
  have hG0 : Measurable G := hG.mono (completedFactor_le μ _) le_rfl
  have hGn0 l : Measurable (Gn l) := (hGn l).mono (hm _) le_rfl
  have hcond := randomConditionalEntropy_tendsto_condition μ F hF hGn0 hG0 ht
  apply ge_of_tendsto hcond
  exact Eventually.of_forall fun l => (hr (n l)).trans
    (randomConditionalEntropy_measurable_factor μ F (Gn l) (K (n l)) hF (hK _) (hGn l))
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

lemma integerWord_conditional_succ (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (G : Ω → B) (hG : Measurable G) (t : ℤ) (n : ℕ) :
    randomConditionalEntropy μ (integerWord F t (n+1)) G =
      randomConditionalEntropy μ (integerWord F t n) G +
      randomConditionalEntropy μ (F (t+n)) (fun x => (G x,integerWord F t n x)) := by
  have he : randomConditionalEntropy μ (integerWord F t (n+1)) G =
      randomConditionalEntropy μ (fun x => (integerWord F t n x,F (t+n) x)) G := by
    apply randomConditionalEntropy_mutual_factor μ _ _ G (measurable_integerWord F hF _ _)
      ((measurable_integerWord F hF _ _).prodMk (hF _)) hG
      (fun z => (fun i : Fin n => z i.castSucc,z (Fin.last n))) (fun z => Fin.snoc z.1 z.2)
    · rfl
    · funext x i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply,Fin.snoc_last,integerWord,Fin.val_last]
      · simp only [Function.comp_apply,Fin.snoc_castSucc,integerWord,Fin.val_castSucc]
  rw [he,randomConditionalEntropy_chain μ _ _ _ (hF _) (measurable_integerWord F hF _ _) hG]

lemma integerWord_conditional_le_sum (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (G : Ω → B) (hG : Measurable G) (t : ℤ) (n : ℕ) :
    randomConditionalEntropy μ (integerWord F t n) G ≤
      ∑ j ∈ Finset.range n, randomConditionalEntropy μ (F (t+j)) G := by
  induction n with
  | zero => simp [randomConditionalEntropy_fintype_one μ _ G (measurable_integerWord F hF _ _) hG]
  | succ n ih =>
    rw [integerWord_conditional_succ μ F hF G hG t n,Finset.sum_range_succ]
    exact add_le_add ih
      (randomConditionalEntropy_condition_comp μ (F (t+n))
        (fun x => (G x,integerWord F t n x)) (hF _)
        (hG.prodMk (measurable_integerWord F hF _ _)) Prod.fst)

lemma integerWord_conditional_lower (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (G : Ω → B) (hG : Measurable G) (t : ℤ) (n : ℕ) (r : ℝ)
    (hr : ∀ j < n, r ≤ randomConditionalEntropy μ (F (t+j))
      (fun x => (G x,integerWord F t j x))) :
    (n : ℝ) * r ≤ randomConditionalEntropy μ (integerWord F t n) G := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul] using randomConditionalEntropy_nonneg μ _ _ (measurable_integerWord F hF t 0) hG
  | succ n ih =>
    rw [integerWord_conditional_succ μ F hF G hG t n,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact add_le_add (ih (fun j hj => hr j (by omega))) (hr n (by omega))
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] in
lemma processPast_le (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) :
    processPast F t ≤ m₀ := iSup_le fun _n => (measurable_integerWord F hF _ _).comap_le

omit [Nonempty A] in
include m₀ in
lemma processPast_zero_le_full (F : ℤ → Ω → A) : processPast F 0 ≤ processFull F := by
  let _ := m₀
  apply iSup_le
  intro n
  have hh := integerWord_subword_measurable F (-(n:ℤ)) 0 n (2*n+1) (by omega)
  simp only [Nat.cast_zero,add_zero] at hh
  have hh' : MeasurableSpace.comap (integerWord F (0-(n:ℤ)) n) inferInstance ≤
      MeasurableSpace.comap (integerWord F (-(n:ℤ)) (2*n+1)) inferInstance := by
    simpa only [zero_sub] using hh.comap_le
  change _ ≤ ⨆ m : ℕ, MeasurableSpace.comap (integerWord F (-(m:ℤ)) (2*m+1)) inferInstance
  exact le_iSup_of_le n hh'

variable (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t))
    (htrans : ∀ t s x, F (t+s) x = F t (U s x))
    (G : ℤ → Ω → B) (hG : ∀ t, Measurable (G t))
    (hGtrans : ∀ t s x, G (t+s) x = G t (U s x))
    (htail : ∀ t s, Measurable[completedFactor (m₀ := m₀) μ (processPast F t)] (G s))

include htail hF in
lemma tail_word_conditional_lower (n : ℕ) (r : ℝ)
    (hr : ∀ (t : ℤ) (m : ℕ), r ≤ randomConditionalEntropy μ (F t) (integerWord F (t-m) m)) :
    (n : ℝ) * r ≤ randomConditionalEntropy μ (integerWord F 0 n) (integerWord G 0 n) := by
  have hg s : Measurable (G s) := (htail 0 s).mono (completedFactor_le μ _) le_rfl
  apply integerWord_conditional_lower μ F hF (integerWord G 0 n) (measurable_integerWord G hg _ _) 0 n r
  intro j hj
  apply conditional_entropy_lower_of_completed μ (fun m => integerWord F ((0+(j:ℤ))-m) m)
    (fun m => measurable_integerWord F hF _ _) (pastWord_comap_mono F _) (F (0+(j:ℤ))) (hF _) _ ?_ r (hr _)
  apply Measurable.prodMk
  · exact @Measurable.of_eval Ω (Fin n) (fun _ => B)
      (completedFactor (m₀ := m₀) μ (processPast F (0+(j:ℤ)))) _
      (integerWord G 0 n) (fun i => htail _ _)
  · have hh : MeasurableSpace.comap (integerWord F 0 j) inferInstance ≤ processPast F (0+(j:ℤ)) := by
      have hh := le_iSup (fun m : ℕ => MeasurableSpace.comap (integerWord F ((0+(j:ℤ))-m) m) inferInstance) j
      simpa only [processPast,zero_add,sub_self] using hh
    exact (comap_measurable _).mono (hh.trans (le_completedFactor μ (processPast_le F hF _))) le_rfl

omit [Nonempty B] in
include hU hF htrans hG hGtrans in
lemma tail_word_conditional_upper (M n : ℕ) (ε : ℝ)
    (he : randomConditionalEntropy μ (G 0) (integerWord F (-(M:ℤ)) (2*M+1)) ≤ ε) :
    randomConditionalEntropy μ (integerWord G 0 n) (integerWord F (-(M:ℤ)) (n+2*M)) ≤ n*ε := by
  apply (integerWord_conditional_le_sum μ G hG _ (measurable_integerWord F hF _ _) 0 n).trans
  calc
    _ ≤ ∑ j ∈ Finset.range n, ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hs := integerWord_subword_measurable F (-(M:ℤ)) j (2*M+1) (n+2*M) (by omega)
      have hc := randomConditionalEntropy_measurable_factor μ (G (0+(j:ℤ)))
        (integerWord F (-(M:ℤ)+(j:ℤ)) (2*M+1)) (integerWord F (-(M:ℤ)) (n+2*M))
        (hG _) (measurable_integerWord F hF _ _) hs
      have hf : G (0+(j:ℤ)) = G 0 ∘ U j := funext fun x => hGtrans 0 j x
      rw [integerWord_translate U F htrans,hf,
        randomConditionalEntropy_measurePreserving μ μ (hU j) _ _ (hG _) (measurable_integerWord F hF _ _)] at hc
      simpa only [hf] using hc.trans he
    _ = n*ε := by simp

include hU hF htrans hG hGtrans htail in

theorem tail_process_entropy_zero :
    Tendsto (fun n : ℕ => randomEntropy μ (integerWord G 0 n) / n) atTop (𝓝 0) := by
  obtain ⟨h,hpos,hlower,hrate⟩ := stationary_entropy_rate μ U hU F hF htrans
  apply entropy_zero_of_tail_bounds (fun n => randomEntropy μ (integerWord F 0 n))
    (fun n => randomEntropy μ (integerWord G 0 n)) h hrate
    (fun n => randomEntropy_nonneg μ _ (measurable_integerWord G hG _ _))
  intro ε hε
  have hfull : Measurable[completedFactor (m₀ := m₀) μ (processFull F)] (G 0) :=
    (htail 0 0).mono (completedFactor_mono μ (processPast_zero_le_full F)) le_rfl
  obtain ⟨M,hM⟩ := exists_conditional_entropy_lt_of_completed μ
    (fun m => integerWord F (-(m:ℤ)) (2*m+1)) (fun m => measurable_integerWord F hF _ _)
    (windowWord_comap_mono F) (G 0) hfull ε hε
  refine ⟨2*M,fun n => ?_⟩
  have hlo := tail_word_conditional_lower μ F hF G htail n h hlower
  have hup := tail_word_conditional_upper μ U hU F hF htrans G hG hGtrans M n ε hM.le
  have he : randomEntropy μ (fun x => (integerWord G 0 n x,integerWord F 0 n x)) ≤
      randomEntropy μ (fun x => (integerWord F (-(M:ℤ)) (n+2*M) x,integerWord G 0 n x)) := by
    let e : (Fin (n+2*M) → A) × (Fin n → B) → (Fin n → B) × (Fin n → A) :=
      fun z => (z.2,fun i => z.1 ⟨M+i.val,by omega⟩)
    have heq : (fun x => (integerWord G 0 n x,integerWord F 0 n x)) =
        e ∘ (fun x => (integerWord F (-(M:ℤ)) (n+2*M) x,integerWord G 0 n x)) := by
      funext x
      apply Prod.ext
      · rfl
      · funext i
        dsimp [e,integerWord]
        congr 1
        ring
    rw [heq]
    exact randomEntropy_comp_le _ ((measurable_integerWord F hF _ _).prodMk (measurable_integerWord G hG _ _)) e
  rw [randomEntropy_pair μ _ _ (measurable_integerWord F hF _ _) (measurable_integerWord G hG _ _),
    randomEntropy_pair μ _ _ (measurable_integerWord G hG _ _) (measurable_integerWord F hF _ _),
    integerWord_entropy_translate μ U hU F hF htrans] at he
  linarith
end

section
open MeasureTheory Filter
variable {Ω A : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [MeasurableSpace A]

omit m₀ in
lemma processPast_eq_generators (F : ℤ → Ω → A) (t : ℤ) :
    processPast F t = ⨆ q : {q : ℤ // q < t}, MeasurableSpace.comap (F q) inferInstance := by
  change (⨆ n : ℕ, MeasurableSpace.comap (fun x (i : Fin n) => F (t-(n:ℤ)+(i.val:ℤ)) x) inferInstance) = _
  simp_rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    apply le_iSup_of_le ⟨t-(n:ℤ)+(i.val:ℤ),by omega⟩
    exact le_rfl
  · apply iSup_le
    intro q
    let n := (t-q.val).toNat
    have hn : (n:ℤ) = t-q.val := by dsimp [n]; omega
    have hnpos : 0 < n := by have := q.property; omega
    apply le_iSup_of_le n
    apply le_iSup_of_le (⟨0,hnpos⟩ : Fin n)
    simp only [Nat.cast_zero,add_zero,hn,sub_sub_cancel]
    exact le_rfl

omit m₀ in
lemma processPast_mono (F : ℤ → Ω → A) : Monotone (processPast F) := by
  intro s t h
  rw [processPast_eq_generators,processPast_eq_generators]
  apply iSup_le
  intro q
  exact le_iSup_of_le ⟨q.val,q.property.trans_le h⟩ le_rfl

lemma completedFactor_comap {f : Ω → Ω} (hf : MeasurePreserving f μ μ)
    {m n : MeasurableSpace Ω} (h : MeasurableSpace.comap f m ≤ n) :
    MeasurableSpace.comap f (completedFactor (m₀ := m₀) μ m) ≤ completedFactor (m₀ := m₀) μ n := by
  rintro s ⟨r,hr,rfl⟩
  obtain ⟨hr,v,hv,he⟩ := hr
  change MeasurableSet[m₀] (f ⁻¹' r) ∧ ∃ v, MeasurableSet[n] v ∧ ∀ᵐ x ∂μ, x ∈ f ⁻¹' r ↔ x ∈ v
  let : MeasurableSpace Ω := m₀
  have hfm : @Measurable Ω Ω m₀ m₀ f := hf.measurable
  have hea : ∀ᵐ x ∂μ, f x ∈ r ↔ f x ∈ v :=
    hf.quasiMeasurePreserving.ae he
  exact ⟨hfm hr,f ⁻¹' v,h _ ⟨v,hv,rfl⟩,hea⟩

omit m₀ in
lemma processPast_comap (U : ℤ → Ω → Ω) (F : ℤ → Ω → A)
    (htrans : ∀ t s x, F (t+s) x = F t (U s x)) (t s : ℤ) :
    MeasurableSpace.comap (U s) (processPast F t) ≤ processPast F (t+s) := by
  rw [processPast_eq_generators,MeasurableSpace.comap_iSup,processPast_eq_generators]
  apply iSup_le
  intro q
  rw [MeasurableSpace.comap_comp]
  have he : F (q.val+s) = F q ∘ U s := funext fun x => htrans q s x
  rw [←he]
  exact le_iSup_of_le ⟨q.val+s,by have := q.property; omega⟩ le_rfl

lemma processTail_le (F : ℤ → Ω → A) : processTail μ F ≤ m₀ :=
  (iInf_le _ 0).trans (completedFactor_le μ _)

lemma processTail_le_past (F : ℤ → Ω → A) (t : ℤ) :
    processTail μ F ≤ completedFactor (m₀ := m₀) μ (processPast F t) := by
  have h : -(((-t).toNat : ℕ) : ℤ) ≤ t := by omega
  exact (iInf_le _ ((-t).toNat)).trans (completedFactor_mono μ (processPast_mono F h))

lemma processTail_comap (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (htrans : ∀ t s x, F (t+s) x = F t (U s x)) (s : ℤ) :
    MeasurableSpace.comap (U s) (processTail μ F) ≤ processTail μ F := by
  apply le_iInf
  intro n
  have h := MeasurableSpace.comap_mono (g := U s) (processTail_le_past μ F (-(n:ℤ)-s))
  apply h.trans
  have ht := completedFactor_comap μ (hU s) (processPast_comap U F htrans (-(n:ℤ)-s) s)
  simpa only [sub_add_cancel] using ht

lemma measurable_tail_translate {B : Type*} [MeasurableSpace B]
    (U : ℤ → Ω → Ω) (hU : ∀ s, MeasurePreserving (U s) μ μ)
    (F : ℤ → Ω → A) (htrans : ∀ t s x, F (t+s) x = F t (U s x))
    (g : Ω → B) (hg : Measurable[processTail μ F] g) (s t : ℤ) :
    Measurable[completedFactor (m₀ := m₀) μ (processPast F t)] (g ∘ U s) := by
  have hu : @Measurable Ω Ω (processTail μ F) (processTail μ F) (U s) :=
    measurable_iff_comap_le.mpr (processTail_comap μ U hU F htrans s)
  exact (hg.comp hu).mono (processTail_le_past μ F t) le_rfl
end

open MeasureTheory Filter
open scoped Topology

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω]
lemma timeMap_add (T : Ω ≃ᵐ Ω) (m n : ℤ) : timeMap T (m+n) = timeMap T m ∘ timeMap T n := by
  simp only [timeMap,zpow_add,Equiv.Perm.coe_mul]
lemma timeMap_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T n = (T : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma timeMap_neg_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T (-(n:ℤ)) = (T.symm : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.coe_pow]
  rfl
lemma timeMap_preserving (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ) (n : ℤ) :
    MeasurePreserving (timeMap T n) μ μ := by
  induction n using Int.negInduction with
  | nat n => rw [timeMap_nat]; exact hT.iterate n
  | neg _ n => rw [timeMap_neg_nat]; exact (hT.symm T).iterate n
lemma timeMap_measurable (T : Ω ≃ᵐ Ω) (n : ℤ) : Measurable (timeMap T n) := by
  induction n using Int.negInduction with
  | nat n => rw [timeMap_nat]; exact T.measurable.iterate n
  | neg _ n => rw [timeMap_neg_nat]; exact T.symm.measurable.iterate n
end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] [MeasurableSpace A] [IsProbabilityMeasure μ] in
lemma observableProcess_translate (T : Ω ≃ᵐ Ω) (a : Ω → A) (s t : ℤ) (x : Ω) :
    observableProcess T a (s+t) x = observableProcess T a s (timeMap T t x) := by
  exact congrArg a (congrFun (timeMap_add T s t) x)

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] [IsProbabilityMeasure μ] in
lemma observableProcess_measurable (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a) (q : ℤ) :
    Measurable (observableProcess T a q) := ha.comp (timeMap_measurable T q)

theorem finite_tail_entropy_zero_oai (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (a : Ω → A) (ha : Measurable a) (b : Ω → B) (hb : Measurable[observableTail μ T a] b) :
    Tendsto (fun n : ℕ => randomEntropy μ (fun x => fun i : Fin n => b ((T^[i.val]) x)) / n)
      atTop (𝓝 0) := by
  have hbm : Measurable b := hb.mono (processTail_le μ _) le_rfl
  have hh := tail_process_entropy_zero μ (timeMap T) (timeMap_preserving μ T hT)
    (observableProcess T a) (observableProcess_measurable T a ha) (observableProcess_translate T a)
    (observableProcess T b) (observableProcess_measurable T b hbm) (observableProcess_translate T b)
    (fun t s => measurable_tail_translate μ (timeMap T) (timeMap_preserving μ T hT)
      (observableProcess T a) (observableProcess_translate T a) b hb s t)
  change Tendsto (fun n : ℕ => randomEntropy μ (fun x => fun i : Fin n => b (timeMap T (0+(i.val:ℤ)) x)) / n) atTop (𝓝 0) at hh
  simpa only [zero_add,timeMap_nat] using hh
end

open MeasureTheory Filter
open scoped Topology BigOperators

end Rokhlin

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Rokhlin.finite_tail_entropy_zero_oai.{u_1, u_2, u_3} := @OAI.Rokhlin.finite_tail_entropy_zero_oai.{u_1, u_2, u_3}
