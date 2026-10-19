-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.expected_grid_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:38:03.305338+00:00
-- url     : https://prove2.me/submissions/05095ee6-23aa-46ba-a495-44c6c2240cb0

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/TypedEntropy.lean:L120-L150
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.expected_grid_upper. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_eq_sum
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_normalize
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_random_observation_entropy
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_random_observation_integrable
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_relativeLabel_mem
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_words

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem negMulLog_sum_le {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  have hterm : ∀ i ∈ s,
      -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonpos_left
        (Real.log_le_log h (Finset.single_le_sum hp hi)) (neg_nonpos.mpr (hp i hi))
  have heq : (∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j)) =
      Real.negMulLog (∑ i ∈ s, p i) := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rfl
  rw [← heq]
  exact Finset.sum_le_sum hterm

theorem observableEntropy_le {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ entropy s p := by
  classical
  calc
    observableEntropy s p f ≤
        ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), Real.negMulLog (p a) := by
      apply Finset.sum_le_sum
      intro b _
      exact negMulLog_sum_le _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = entropy s p :=
      Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

theorem entropy_mixture {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (w : β → ℝ) (p : β → α → ℝ)
    (hw : ∀ b ∈ t, 0 ≤ w b) (hw1 : ∑ b ∈ t, w b = 1)
    (hp : ∀ b ∈ t, ∀ a ∈ s, 0 ≤ p b a) :
    ∑ b ∈ t, w b * entropy s (p b) ≤
      entropy s (fun a => ∑ b ∈ t, w b * p b a) := by
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  exact Real.concaveOn_negMulLog.le_map_sum hw hw1 (fun b hb => hp b hb a ha)

theorem entropy_joint_le {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b)
    (hp1 : ∑ a ∈ s, ∑ b ∈ t, p a b = 1) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) ≤
      entropy s (fun a => ∑ b ∈ t, p a b) + entropy t (fun b => ∑ a ∈ s, p a b) := by
  let r := fun a => ∑ b ∈ t, p a b
  have hr : ∀ a ∈ s, 0 ≤ r a := fun a ha => Finset.sum_nonneg (hp a ha)
  have hterm : ∀ a ∈ s, ∀ b ∈ t, r a * (p a b / r a) = p a b := by
    intro a ha b hb
    by_cases h : r a = 0
    · have hl := Finset.single_le_sum (hp a ha) hb
      have hz : p a b = 0 := le_antisymm (h ▸ hl) (hp a ha b hb)
      simp [hz]
    · exact mul_div_cancel₀ _ h
  have hc := entropy_mixture t s r (fun a b => p a b / r a) hr hp1
    (fun a ha b hb => div_nonneg (hp a ha b hb) (hr a ha))
  have hmix : entropy t (fun b => ∑ a ∈ s, r a * (p a b / r a)) =
      entropy t (fun b => ∑ a ∈ s, p a b) := by
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    exact Finset.sum_congr rfl (fun a ha => hterm a ha b hb)
  rw [hmix] at hc
  calc
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
        ∑ a ∈ s, entropy t (p a) := by simp only [entropy, Finset.sum_product]
    _ = entropy s r + ∑ a ∈ s, r a * entropy t (fun b => p a b / r a) := by
      simp only [entropy, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      exact entropy_normalize t (p a) (hp a ha)
    _ ≤ _ := add_le_add le_rfl hc

theorem observableEntropy_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) : observableEntropy s p f = entropy t (mass s p f) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hf a ha
  · intro b _ hb
    rw [mass_eq_zero_of_not_mem s p f hb, Real.negMulLog_zero]

theorem observableEntropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (g ∘ f) ≤ observableEntropy s p f := by
  rw [observableEntropy_comp]
  exact observableEntropy_le _ _ _ (fun b _ => mass_nonneg s p f hp b)

theorem mass_pair_fst {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (b : β) :
    ∑ c ∈ s.image g, mass s p (fun a => (f a, g a)) (b, c) = mass s p f b := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hg : g a ∈ s.image g := Finset.mem_image_of_mem g ha
  by_cases hf : f a = b
  · simp [hf, hg]
  · simp [hf]

theorem mass_pair_snd {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) :
    ∑ b ∈ s.image f, mass s p (fun a => (f a, g a)) (b, c) = mass s p g c := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hf : f a ∈ s.image f := Finset.mem_image_of_mem f ha
  by_cases hg : g a = c
  · simp [hg, hf]
  · simp [hg]

theorem observableEntropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p (fun a => (f a, g a)) ≤
      observableEntropy s p f + observableEntropy s p g := by
  classical
  rw [observableEntropy_on_superset s (s.image f ×ˢ s.image g) p _
    (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem f ha, Finset.mem_image_of_mem g ha⟩)]
  have h := entropy_joint_le (s.image f) (s.image g)
    (fun b c => mass s p (fun a => (f a, g a)) (b, c))
    (fun b _ c _ => mass_nonneg s p _ hp _) ?_
  · simpa only [mass_pair_fst, mass_pair_snd, observableEntropy] using h
  · simpa only [mass_pair_fst, mass_sum] using hp1

theorem conditionalEntropy_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f g ≤ observableEntropy s p f := by
  dsimp only [conditionalEntropy]
  linarith [observableEntropy_pair_le s p f g hp hp1]

theorem observableEntropy_le_log_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f ≤ Real.log t.card := by
  rw [observableEntropy_on_superset s t p f hf]
  apply entropy_le_log_card _ _ (fun b _ => mass_nonneg s p f hp b)
  have h := sum_mass_mul s t p f (fun _ => 1) hf
  simpa only [mul_one, hp1] using h

theorem observableEntropy_congr {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (f g : α → β)
    (hp : ∀ x ∈ s, p x = q x) (hf : ∀ x ∈ s, f x = g x) :
    observableEntropy s p f = observableEntropy s q g := by
  classical
  have hi : s.image f = s.image g := Finset.image_congr hf
  have hm : ∀ b, mass s p f b = mass s q g b := by
    intro b
    simp only [mass, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp x hx, hf x hx]
  simp only [observableEntropy, hi]
  rw [show mass s p f = mass s q g from funext hm]

theorem observableEntropy_le_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ] [Nonempty β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, g x = g y → f x = f y) :
    observableEntropy s p f ≤ observableEntropy s p g := by
  classical
  let h : γ → β := fun c => if hc : ∃ x ∈ s, g x = c then f hc.choose else Classical.choice inferInstance
  have hf : ∀ x ∈ s, (h ∘ g) x = f x := by
    intro x hx
    dsimp only [Function.comp_apply,h]
    rw [dite_eq_left ⟨x,hx,rfl⟩]
    exact hfg _ (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).1
      x hx (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).2
  rw [← observableEntropy_congr s p p (h ∘ g) f (fun _ _ => rfl) hf]
  exact observableEntropy_comp_le s p g h hp

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedEntropy ----
namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators
open FiniteEntropy

theorem entropy_expectation {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (f : α → γ) :
    (∑ a, p a*observableEntropy (fiber tag a) (fun v => p v/mass p tag a) f)=
      conditionalEntropy Finset.univ p f tag := by
  classical
  rw [conditionalEntropy_eq_sum _ _ _ _ (fun a _ => (hp a).le)]
  symm
  convert FiniteEntropy.sum_mass_mul Finset.univ (Finset.univ.image tag) p tag
    (fun c => observableEntropy (Finset.univ.filter (fun a => tag a=c))
      (fun a => p a/FiniteEntropy.mass Finset.univ p tag c) f)
    (fun a ha => Finset.mem_image_of_mem tag ha) using 1
  rfl

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators
open MeasureEntropy

theorem shifted_grid_compare {α : Type uα} (s : Finset α) (p f : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a=1)
    {ρ : ℝ} (hρ : 0 < ρ) (u v : ℝ) :
    observableEntropy s p (fun a => label ρ u (f a)) ≤
      observableEntropy s p (fun a => label ρ v (f a))+Real.log 2 := by
  classical
  let g := fun a => label ρ v (f a)
  let r := fun a => relativeLabel ρ ρ u v (f a)
  have hr : ∀ a ∈ s, r a ∈ Finset.Icc (0 : ℤ) 1 := by
    intro a _
    simpa only [div_self hρ.ne',Int.ceil_one] using relativeLabel_mem hρ hρ u v (f a)
  have he := observableEntropy_le_of_fibers s p (fun a => label ρ u (f a))
    (fun a => (g a,r a)) hp (by
      intro a _ b _ hab
      obtain ⟨h1,h2⟩ := Prod.mk.inj hab
      dsimp [r,relativeLabel] at h2
      change label ρ v (f a)=label ρ v (f b) at h1
      rw [h1] at h2
      linarith)
  have hh := observableEntropy_pair_le s p g r hp hp1
  have hle := observableEntropy_le_log_on_superset s (Finset.Icc (0 : ℤ) 1) p r hr hp hp1
  norm_num at hle
  change observableEntropy s p r ≤ Real.log 2 at hle
  change _ ≤ observableEntropy s p g+Real.log 2
  linarith

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition FiniteEntropy MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem expected_grid_comparison (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (y : ℝ) :
    (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ≤
      observableEntropy Finset.univ (S.wordWeight (n := n)) (fun v => ⌊S.wordMap v y/ρ⌋)+Real.log 2 := by
  classical
  let p := S.wordWeight (n := n)
  let t := tagWord tag (n := n)
  have hp : ∀ v, 0 < p v := S.wordWeight_pos
  have hlocal (w : Fin n → α) :
      (law S tag w).gridEntropy ρ*Real.log 2 ≤
        observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
          (fun v => ⌊S.wordMap v y/ρ⌋)+Real.log 2 := by
    have hc := shifted_grid_compare (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
      (fun v => (S.completeMap v).2)
      (fun v _ => (div_pos (hp v) (mass_pos p hp t w)).le) (fiber_normalized_sum p hp t w)
      hρ 0 ((S.completeMap w).1*y/ρ)
    have hobs : observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
        (fun v => label ρ ((S.completeMap w).1*y/ρ) (S.completeMap v).2) =
        observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
          (fun v => ⌊S.wordMap v y/ρ⌋) := by
      apply observableEntropy_congr _ _ _ _ _ (fun _ _ => rfl)
      intro v hv
      have hv' : t v=t w := (Finset.mem_filter.mp hv).2
      have hsl : (S.completeMap v).1=(S.completeMap w).1 := by
        rw [S.completeMap_slope,S.completeMap_slope]
        exact Finset.prod_congr rfl (fun j _ => hr _ _ (congrFun hv' j))
      unfold label System.wordMap
      rw [hsl]
      congr 1
      ring
    rw [hobs] at hc
    simpa only [law,FiniteCondition.law,Law.ofObservable_gridEntropy,
      div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne',label,add_zero] using hc
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hlocal w) (S.wordWeight_pos w).le)
  simp only [mul_add,Finset.sum_add_distrib,← mul_assoc,← Finset.sum_mul,S.wordWeight_sum,one_mul] at hsum
  rw [entropy_expectation p hp t] at hsum
  have hh := conditionalEntropy_le Finset.univ p (fun v => ⌊S.wordMap v y/ρ⌋) t
    (fun w _ => (hp w).le) (S.wordWeight_sum n)
  exact hsum.trans (by linarith)

theorem word_map_ae (S : System α) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {n : ℕ} (w : Fin n → α) {P : ℝ → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ.map (S.wordMap w), P x := by
  classical
  rw [ae_iff] at hP ⊢
  have hle : ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) ≤ μ := by
    conv_rhs => rw [S.selfSimilar_words μ hμ n]
    exact Finset.single_le_sum (fun v (_ : v ∈ Finset.univ) =>
      (bot_le : (0 : Measure ℝ) ≤ ENNReal.ofReal (S.wordWeight v) • μ.map (S.wordMap v)))
      (Finset.mem_univ w)
  have hz : ENNReal.ofReal (S.wordWeight w)*(μ.map (S.wordMap w)) {x | ¬P x}=0 := by
    apply le_antisymm _ (zero_le : (0 : ℝ≥0∞) ≤ _)
    simpa only [Measure.smul_apply,smul_eq_mul,hP] using hle {x | ¬P x}
  exact (mul_eq_zero.mp hz).resolve_left (ENNReal.ofReal_ne_zero_iff.mpr (S.wordWeight_pos w))

theorem expected_grid_upper (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ≤
      grid μ ρ 0+Real.log 2 := by
  classical
  obtain ⟨B,_,hB⟩ := hc
  let s := Finset.Icc ⌊-B/ρ+(0 : ℝ)⌋ ⌊B/ρ+(0 : ℝ)⌋
  have hs (w : Fin n → α) : ∀ᵐ y ∂μ, label ρ 0 (S.wordMap w y) ∈ s := by
    apply (ae_map_iff (S.wordMap_measurable w).aemeasurable
      ((label_measurable ρ 0) s.finite_toSet.measurableSet)).mp
    exact word_map_ae S μ hμ w (label_ae_finite μ hρ hB)
  have hj := random_observation_entropy μ μ S.wordWeight (fun w => (S.wordWeight_pos w).le)
    (S.wordWeight_sum n) S.wordMap S.wordMap_measurable (S.selfSimilar_words μ hμ n)
    (label ρ 0) (label_measurable ρ 0) s hs
  have hi := random_observation_integrable μ S.wordWeight (fun w => (S.wordWeight_pos w).le)
    (S.wordWeight_sum n) (fun w y => label ρ 0 (S.wordMap w y))
    (fun w => (label_measurable ρ 0).comp (S.wordMap_measurable w)) s hs
  have hpoint := integral_mono (integrable_const
    ((∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2))
    (hi.add (integrable_const (Real.log 2)))
    (fun y => by
      change _ ≤ observableEntropy Finset.univ S.wordWeight
        (fun v => label ρ 0 (S.wordMap v y))+Real.log 2
      simpa only [label,add_zero] using expected_grid_comparison S tag hr hρ y)
  change (∫ _ : ℝ, (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ∂μ) ≤
    (∫ y, observableEntropy Finset.univ S.wordWeight (fun v => label ρ 0 (S.wordMap v y))+Real.log 2 ∂μ) at hpoint
  rw [integral_add hi (integrable_const _)] at hpoint
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hpoint
  exact hpoint.trans (by simpa only [grid,add_comm] using add_le_add_right hj (Real.log 2))

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition FiniteEntropy MeasureEntropy
open scoped BigOperators ENNReal


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.expected_grid_upper.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.expected_grid_upper.{uα,uβ}
