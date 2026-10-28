-- Prove2me | solution 1 for OAI.SharpLogRamsey.LowerTransfer.prime_construction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:34:23.271048+00:00
-- url     : https://prove2.me/submissions/e6c693bf-7981-4a08-abf6-8cd11025a295

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_Marking_eventually_tracked_step

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_FiniteStreamTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FiniteStreamTail
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*} [Fintype α]

variable [Nonempty α]

omit [Nonempty α] [Fintype α] in
lemma hits_embedding {N n : ℕ} (S : Finset α) (z : Fin N→α) (e : Fin n↪Fin N) :
    hits S (z∘e)≤hits S z := by
  let A := univ.filter (fun i : Fin n=>z (e i)∈S)
  have he : A.map e⊆univ.filter (fun i : Fin N=>z i∈S) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
  simpa only [card_map,A,hits,Function.comp_def] using card_le_card he

end
end SharpLogRamsey.FiniteStreamTail

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection

variable {α β : Type*} [Fintype α] [Fintype β]

theorem entropy_ge_neg_log (p : Law α) {c : ℝ} (_hc : 0 < c)
    (hcap : ∀ a, p.mass a ≤ c) : -Real.log c ≤ entropy p := by
  have h : ∑ a, p.mass a * Real.log (p.mass a) ≤ Real.log c := by
    calc
      _ ≤ ∑ a, p.mass a * Real.log c := by
        apply Finset.sum_le_sum
        intro a _
        rcases (p.nonneg a).eq_or_lt with hz | hp
        · simp [← hz]
        · exact mul_le_mul_of_nonneg_left (Real.log_le_log hp (hcap a)) (p.nonneg a)
      _ = Real.log c := by rw [← Finset.sum_mul, p.total, one_mul]
  exact neg_le_neg h

theorem card_fixed_coordinates {N ℓ : ℕ} (e : Fin ℓ ↪ Fin N)
    (f : Fin ℓ → α) :
    Fintype.card {g : Fin N → α // ∀ i, g (e i) = f i} ≤
      Fintype.card α ^ (N - ℓ) := by
  classical
  let S : Finset (Fin N) := Finset.univ.map e
  have hS : S.card = ℓ := by simp [S]
  have he (i : Fin ℓ) : e i ∈ S := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let restrict : {g : Fin N → α // ∀ i, g (e i) = f i} → ({x // x ∉ S} → α) :=
    fun g x => g.val x.val
  have hi : Function.Injective restrict := by
    intro g h hgh
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact (g.property i).trans (h.property i).symm
    · exact congr_fun hgh ⟨x, hx⟩
  have hc : Fintype.card {x // x ∉ S} = N - ℓ := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, hS]
  simpa only [Fintype.card_fun, hc] using Fintype.card_le_of_injective restrict hi

theorem card_occurs {N ℓ : ℕ} (f : Fin ℓ → α) :
    Fintype.card {g : Fin N → α // Occurs f g} ≤
      N.choose ℓ * Fintype.card α ^ (N - ℓ) := by
  classical
  let cyl (S : Positions N ℓ) : Finset (Fin N → α) :=
    {g | ∀ i, g (positionMap S i) = f i}
  have h : ({g | Occurs f g} : Finset (Fin N → α)) = Finset.univ.biUnion cyl := by
    ext g; simp [cyl, Occurs]
  rw [Fintype.card_subtype, h]
  calc
    _ ≤ ∑ S : Positions N ℓ, (cyl S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S : Positions N ℓ, Fintype.card α ^ (N - ℓ) := by
      apply Finset.sum_le_sum
      intro S _
      simpa only [cyl, ← Fintype.card_subtype] using card_fixed_coordinates (positionMap S) f
    _ = N.choose ℓ * Fintype.card α ^ (N - ℓ) := by simp [Fintype.card_finset_len]

theorem card_occurs_two {N ℓ : ℕ} (f f' : Fin ℓ → α) :
    Fintype.card {g : Fin N → α // Occurs f g ∨ Occurs f' g} ≤
      2 * N.choose ℓ * Fintype.card α ^ (N - ℓ) := by
  classical
  have h : ({g | Occurs f g ∨ Occurs f' g} : Finset (Fin N → α)) =
      ({g | Occurs f g} : Finset _) ∪ ({g | Occurs f' g} : Finset _) := by ext; simp
  rw [Fintype.card_subtype, h]
  have h1 := card_occurs f (N := N)
  have h2 := card_occurs f' (N := N)
  rw [Fintype.card_subtype] at h1 h2
  exact (Finset.card_union_le _ _).trans (by nlinarith)

theorem selected_atom_bound [Nonempty α] {N ℓ : ℕ} (hℓ : ℓ ≤ N)
    (p : Law ((Fin N → α) × (Fin ℓ → α)))
    (reverse : (Fin ℓ → α) → (Fin ℓ → α)) {C : ℝ} (hC : 0 < C)
    (hdom : ∀ g, p.fst.mass g ≤ C / (Fintype.card α : ℝ)^N)
    (hselect : ∀ g f, p.mass (g,f) ≠ 0 → Occurs f g ∨ Occurs (reverse f) g)
    (f : Fin ℓ → α) :
    p.snd.mass f ≤ 2 * C * N.choose ℓ / (Fintype.card α : ℝ)^ℓ := by
  let a : ℝ := Fintype.card α
  have ha : 0 < a := by
    dsimp [a]; exact_mod_cast (Fintype.card_pos (α := α))
  let E : Finset (Fin N → α) := {g | Occurs f g ∨ Occurs (reverse f) g}
  have hcard : (E.card : ℝ) ≤ 2 * N.choose ℓ * a^(N-ℓ) := by
    have hc := card_occurs_two f (reverse f) (N := N)
    rw [Fintype.card_subtype] at hc
    dsimp [E, a]
    exact_mod_cast hc
  have hsum : p.snd.mass f ≤ (E.card : ℝ) * (C / a^N) := by
    calc
      _ = ∑ g, p.mass (g,f) := rfl
      _ ≤ ∑ g, if g ∈ E then C / a^N else 0 := by
        apply Finset.sum_le_sum
        intro g _
        by_cases hg : g ∈ E
        · rw [ite_eq_left hg]
          exact (Finset.single_le_sum (fun b _ => p.nonneg (g,b))
            (Finset.mem_univ f)).trans (hdom g)
        · rw [ite_eq_right hg]
          have hz : p.mass (g,f) = 0 := by
            by_contra h
            exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hselect g f h⟩)
          rw [hz]
      _ = _ := by simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (2 * (N.choose ℓ : ℝ) * a^(N-ℓ)) * (C / a^N) :=
      hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = 2 * C * N.choose ℓ / a^ℓ := by
      have hp : a^N = a^(N-ℓ) * a^ℓ := by rw [← pow_add, Nat.sub_add_cancel hℓ]
      rw [hp]
      field_simp

theorem selected_entropy_bound [Nonempty α] {N ℓ : ℕ} (hℓ : ℓ ≤ N)
    (p : Law ((Fin N → α) × (Fin ℓ → α)))
    (reverse : (Fin ℓ → α) → (Fin ℓ → α)) {C : ℝ} (hC : 0 < C)
    (hdom : ∀ g, p.fst.mass g ≤ C / (Fintype.card α : ℝ)^N)
    (hselect : ∀ g f, p.mass (g,f) ≠ 0 → Occurs f g ∨ Occurs (reverse f) g) :
    (ℓ : ℝ) * Real.log (Fintype.card α) - Real.log (2 * C * N.choose ℓ)
      ≤ entropy p.snd := by
  have ha : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hchoose : (0 : ℝ) < N.choose ℓ := by exact_mod_cast Nat.choose_pos hℓ
  have h := entropy_ge_neg_log p.snd
    (c := 2 * C * N.choose ℓ / (Fintype.card α : ℝ)^ℓ) (by positivity)
    (selected_atom_bound hℓ p reverse hC hdom hselect)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at h
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem entropy_subadditive (p : Law (α × β)) : entropy p ≤ entropy p.fst+entropy p.snd := by
  have h := mutualInfo_nonneg p
  unfold mutualInfo at h
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem Law.le_map (p : Law α) (f : α → β) (a : α) :
    p.mass a ≤ (p.map f).mass (f a) := by
  apply single_le_sum (fun b hb => p.nonneg b)
  simp

theorem entropy_map_le (p : Law α) (f : α → β) : entropy (p.map f) ≤ entropy p := by
  rw [entropy_map,entropy]
  apply neg_le_neg
  apply sum_le_sum
  intro a ha
  by_cases hz : p.mass a = 0
  · simp [hz]
  apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
  exact Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz)) (p.le_map f a)

theorem Law.snd_mul_condFst (p : Law (α × β)) (a : α) (b : β) :
    p.snd.mass b*(p.condFst b).mass a = p.mass (a,b) := by
  by_cases h : p.snd.mass b = 0
  · rw [h,zero_mul]
    exact (le_antisymm (by simpa [h] using p.le_snd a b) (p.nonneg _)).symm
  · rw [p.condFst_mass b h a]
    field_simp

theorem entropy_chain (p : Law (α × β)) :
    entropy p = entropy p.snd+∑ b, p.snd.mass b*entropy (p.condFst b) := by
  have pointwise (a : α) (b : β) :
      p.mass (a,b)*Real.log (p.mass (a,b)) =
      p.mass (a,b)*Real.log (p.snd.mass b)+
      p.snd.mass b*((p.condFst b).mass a*Real.log ((p.condFst b).mass a)) := by
    by_cases hp : p.mass (a,b) = 0
    · have hh := p.snd_mul_condFst a b
      rw [hp] at hh
      simp only [hp,zero_mul,zero_add]
      rw [← mul_assoc,hh,zero_mul]
    have hs : 0 < p.snd.mass b := (lt_of_le_of_ne (p.nonneg (a,b)) (Ne.symm hp)).trans_le (p.le_snd a b)
    rw [p.condFst_mass b hs.ne', Real.log_div hp hs.ne']
    field_simp
    ring
  unfold entropy
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [pointwise, sum_add_distrib, ← mul_sum, ← sum_mul]
  change -((∑ b, p.snd.mass b*Real.log (p.snd.mass b))+
    ∑ b, p.snd.mass b*∑ a, (p.condFst b).mass a*Real.log ((p.condFst b).mass a)) = _
  simp only [mul_neg, sum_neg_distrib]
  ring

end SharpLogRamsey.Selection
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DivergenceMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem entropy_cond_chain (p : Law α) (f : α → β) (g : α → γ) :
    entropy (p.map (fun a => (g a,f a))) = entropy (p.map f)+
      ∑ b, (p.map f).mass b*entropy ((p.cond f b).map g) := by
  let q := p.map (fun a => (g a,f a))
  have he : q.snd = p.map f := by rw [← Law.map_snd, Law.map_map]; rfl
  have hm (b : β) : (p.map f).mass b*entropy (q.condFst b) =
      (p.map f).mass b*entropy ((p.cond f b).map g) := by
    by_cases hb : (p.map f).mass b = 0
    · simp [hb]
    congr 1
    congr 1
    ext c
    apply (mul_left_cancel₀ hb)
    rw [← he, q.snd_mul_condFst, he, p.cond_map_weight]
  rw [entropy_chain, he]
  congr 1
  exact sum_congr rfl fun b hb => hm b

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Law.absContinuous_pi (p : Law (ι → β)) :
    p.AbsolutelyContinuous (Law.pi p.marginal) := by
  intro x hz
  change (∏ i, (p.marginal i).mass (x i)) = 0 at hz
  obtain ⟨i,hi⟩ := (prod_eq_zero_iff).mp hz
  have hh : p.mass x ≤ (p.marginal i).mass (x i) := p.le_map (fun y => y i) x
  exact le_antisymm (hi.2 ▸ hh) (p.nonneg _)

theorem totalCorrelation_eq_divergence (p : Law (ι → β)) :
    totalCorrelation p = divergence p (Law.pi p.marginal) := by
  have pointwise (x : ι → β) :
      p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i))) =
      p.mass x*Real.log (p.mass x)-∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) := by
    by_cases hz : p.mass x = 0
    · simp [hz]
    have hp : 0 < p.mass x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hz)
    have hm (i : ι) : 0 < (p.marginal i).mass (x i) := hp.trans_le (p.le_map _ x)
    rw [Real.log_div hz (prod_ne_zero_iff.mpr fun i hi => (hm i).ne'),
      Real.log_prod (fun i hi => (hm i).ne'),mul_sub,mul_sum]
  have hs : ∑ x, ∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) =
      ∑ i, ∑ b, (p.marginal i).mass b*Real.log ((p.marginal i).mass b) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    exact (p.sum_map (fun x => x i) (fun b => Real.log ((p.marginal i).mass b))).symm
  unfold divergence
  change _ = ∑ x, p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i)))
  simp_rw [pointwise]
  rw [sum_sub_distrib,hs]
  unfold totalCorrelation entropy
  rw [sum_neg_distrib]
  ring

theorem totalCorrelation_nonneg (p : Law (ι → β)) : 0 ≤ totalCorrelation p := by
  rw [totalCorrelation_eq_divergence]
  exact divergence_nonneg _ _ p.absContinuous_pi

theorem entropy_subadditive_pi (p : Law (ι → β)) :
    entropy p ≤ ∑ i, entropy (p.marginal i) := by
  have h := totalCorrelation_nonneg p
  unfold totalCorrelation at h
  linarith

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RemainingEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.Selection
variable {Ω α Γ A : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype A]

lemma entropy_mapped_support (p : Law Ω) (F : Ω → α) (S : Finset α)
    (hS : ∀ x, p.mass x ≠ 0 → F x ∈ S) : entropy (p.map F) ≤ Real.log S.card := by
  apply entropy_le_log_card
  intro a ha
  by_contra hn
  obtain ⟨x,hx,rfl⟩ := p.map_support F a hn
  exact ha (hS x hx)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_AuxiliaryLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped Classical BigOperators

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.onEvent_mean (p : Law α) (E : Finset α) (hE : 0<p.event E) (f : α→ℝ) :
    ∑ a : E, (p.onEvent E hE).mass a*f a = (∑ a∈E, p.mass a*f a)/p.event E := by
  simp only [Law.onEvent,div_mul_eq_mul_div,←sum_div]
  congr 1
  exact sum_coe_sort E (fun a => p.mass a*f a)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_LevelLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_incident_points [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1)
    (b : Projectivization K (Module.Dual K V)) :
    Nat.card {a : Projectivization K V // Incident a b} =
      ∑ i ∈ Finset.range d, Nat.card K ^ i := by
  let e : {a : Projectivization K V // Incident a b} ≃
      {a : Projectivization K V // a.submodule ≤ LinearMap.ker b.rep} :=
    Equiv.subtypeEquivRight (fun a => incident_iff_submodule a b)
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv (LinearMap.ker b.rep))]
  apply Projectivization.card_of_finrank
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  omega

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking

section FinitePotential
variable {Y : Type*} [Fintype Y]

theorem below_antitone {r r' : Y → ℕ} (h : ∀ y, r y ≤ r' y) (l : ℕ) :
    below r' l ⊆ below r l := by
  intro y hy
  simp only [below, mem_filter, mem_univ, true_and] at *
  exact (h y).trans hy

theorem potential_nonneg (D : ℕ) (r : Y → ℕ) : 0 ≤ potential D r := by
  apply sum_nonneg
  intro l hl
  apply Real.log_nonneg
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

theorem potential_le (D : ℕ) (r : Y → ℕ) :
    potential D r ≤ (D+1)*Real.log (Fintype.card Y + 1 : ℝ) := by
  calc
    _ ≤ ∑ _l ∈ range (D+1), Real.log (Fintype.card Y + 1 : ℝ) := by
      apply sum_le_sum
      intro l hl
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_right (card_le_univ _) 1
    _ = _ := by simp

theorem log_drop {n m δ : ℝ} (hn : 1 ≤ n) (hm : 0 ≤ m)
    (hδ : 0 ≤ δ) (hdrop : m ≤ n - δ*n) :
    δ/2 ≤ Real.log (n+1) - Real.log (m+1) := by
  have hn0 : 0 < n+1 := by linarith
  have hm0 : 0 < m+1 := by linarith
  have hratio : 0 < (m+1)/(n+1) := div_pos hm0 hn0
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hm0.ne' hn0.ne'] at hlog
  have hfrac : (m+1)/(n+1) ≤ 1-δ/2 := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hn)]
  linarith

theorem potential_drop {D l : ℕ} {r r' : Y → ℕ} {δ : ℝ}
    (hl : l ≤ D) (hmono : ∀ y, r y ≤ r' y)
    (hn : (below r l).Nonempty) (hδ : 0 ≤ δ)
    (hdrop : ((below r' l).card : ℝ) ≤ (below r l).card - δ*(below r l).card) :
    δ/2 ≤ potential D r - potential D r' := by
  have hle i : Real.log ((below r' i).card + 1 : ℝ) ≤
      Real.log ((below r i).card + 1 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right (card_le_card (below_antitone hmono i)) 1
  rw [potential, potential, ← sum_sub_distrib]
  calc
    _ ≤ Real.log ((below r l).card + 1 : ℝ) - Real.log ((below r' l).card + 1 : ℝ) := by
      apply log_drop _ (by positivity) hδ hdrop
      exact_mod_cast (card_pos.mpr hn)
    _ ≤ ∑ i ∈ range (D+1),
        (Real.log ((below r i).card + 1 : ℝ) - Real.log ((below r' i).card + 1 : ℝ)) := by
      exact single_le_sum (fun i hi => sub_nonneg.mpr (hle i)) (mem_range.mpr (by omega))

theorem below_card_le_of_max {r : Y → ℕ} {l : ℕ}
    (hmax : ∀ j ≤ l, (level r j).card ≤ (level r l).card) :
    (below r l).card ≤ (l+1)*(level r l).card := by
  have heq : below r l = (range (l+1)).biUnion (level r) := by
    ext y
    simp [below, level]
  rw [heq]
  calc
    _ ≤ ∑ j ∈ range (l+1), (level r j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ range (l+1), (level r l).card :=
      sum_le_sum fun j hj => hmax j (by simpa using hj)
    _ = _ := by simp
end FinitePotential

section State
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in
theorem le_update (W : State (K:=K) (V:=V)) (a : Module.Dual K V)
    (b y : Points (K:=K) (V:=V)) : W y ≤ update W a b y := by
  unfold update
  split_ifs
  · exact le_sup_left
  · exact le_rfl

omit [Fintype (Projectivization K V)] in
theorem ranks_update_mono (W : State (K:=K) (V:=V)) (a : Module.Dual K V)
    (b y : Points (K:=K) (V:=V)) : ranks W y ≤ ranks (update W a b) y :=
  Submodule.finrank_mono (le_update W a b y)

omit [Fintype (Projectivization K V)] in
theorem ranks_lt_update (W : State (K:=K) (V:=V)) (a : Module.Dual K V)
    (b y : Points (K:=K) (V:=V)) (ha : a y.rep = 0) (hb : ¬ b.submodule ≤ W y) :
    ranks W y < ranks (update W a b) y := by
  apply Submodule.finrank_lt_finrank_of_lt
  rw [update, ite_eq_left ha]
  refine lt_of_le_of_ne le_sup_left ?_
  intro he
  apply hb
  have h : b.submodule ≤ W y ⊔ b.submodule := le_sup_right
  rwa [← he] at h

theorem expensive_drop (W : State (K:=K) (V:=V)) {q : ℝ} (hq : 0 < q)
    {l D : ℕ} (hl : l ≤ D)
    (hmax : ∀ j ≤ l, (level (ranks W) j).card ≤ (level (ranks W) l).card)
    (a : Module.Dual K V) (b : Points (K:=K) (V:=V))
    (hp : ¬ Popular W q l b) (hr : ¬ Poor W q l a) :
    (1/(32*(D+1)*q) : ℝ) ≤
      potential D (ranks W) - potential D (ranks (update W a b)) := by
  let Z := level (ranks W) l
  let H := Z.filter (fun y => a y.rep = 0)
  let B := Z.filter (fun y => b.submodule ≤ W y)
  have hp' : (B.card:ℝ) < Z.card/(16*q) := lt_of_not_ge hp
  have hr' : Z.card/(8*q) < (H.card:ℝ) := lt_of_not_ge hr
  have hZ : Z.Nonempty := by
    apply card_pos.mp
    by_contra! hz
    have hz0 : Z.card = 0 := by omega
    have hB0 : B.card = 0 := by apply Nat.eq_zero_of_le_zero; rw [← hz0]; exact card_filter_le _ _
    rw [hz0, hB0] at hp'
    simp at hp'
  have hU := below_card_le_of_max hmax
  have hUD : (below (ranks W) l).card ≤ (D+1)*Z.card :=
    hU.trans (Nat.mul_le_mul_right _ (by omega))
  have hset : below (ranks (update W a b)) l ⊆ below (ranks W) l \ (H \ B) := by
    intro y hy
    refine mem_sdiff.mpr ⟨below_antitone (ranks_update_mono W a b) l hy, ?_⟩
    intro hb
    obtain ⟨hyH, hyB⟩ := mem_sdiff.mp hb
    obtain ⟨hyZ, ha⟩ := mem_filter.mp hyH
    have ranky : ranks W y = l := by simpa [Z, level] using hyZ
    have hby : ¬ b.submodule ≤ W y := fun hb => hyB (mem_filter.mpr ⟨hyZ,hb⟩)
    have hgt := ranks_lt_update W a b y ha hby
    have hle : ranks (update W a b) y ≤ l := by simpa [below] using hy
    omega
  have hHB : H \ B ⊆ below (ranks W) l := by
    intro y hy
    have hz := (mem_filter.mp (mem_sdiff.mp hy).1).1
    simp only [Z, level, mem_filter, mem_univ, true_and] at hz
    simpa only [below, mem_filter, mem_univ, true_and] using hz.le
  have hcard : (below (ranks (update W a b)) l).card + (H \ B).card ≤
      (below (ranks W) l).card := by
    have hc := card_le_card hset
    rw [card_sdiff_of_subset hHB] at hc
    have hsmall := card_le_card hHB
    omega
  have hdiff : (H.card:ℝ) - B.card ≤ ((H \ B).card:ℝ) := by
    have hc : H.card ≤ (H \ B).card + B.card := card_le_card_sdiff_add_card
    have hc' : (H.card:ℝ) ≤ (H \ B).card + B.card := by exact_mod_cast hc
    linarith
  have hpos : (0:ℝ) < D+1 := by positivity
  have hfrac : ((below (ranks W) l).card : ℝ)/(16*(D+1)*q) ≤
      (H.card:ℝ)-B.card := by
    have hUD' : ((below (ranks W) l).card : ℝ) ≤ (D+1)*Z.card := by exact_mod_cast hUD
    have h1 : ((below (ranks W) l).card : ℝ)/(16*(D+1)*q) ≤ Z.card/(16*q) := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 16*(D+1)*q)).mpr
      field_simp
      nlinarith
    have h2 : Z.card/(16*q) < (H.card:ℝ)-B.card := by
      have he : (Z.card:ℝ)/(8*q) = 2*(Z.card/(16*q)) := by field_simp; ring
      linarith
    exact h1.trans h2.le
  have hbelow : (below (ranks W) l).Nonempty := by
    obtain ⟨y,hy⟩ := hZ
    refine ⟨y,?_⟩
    have hz : ranks W y = l := by simpa [Z, level] using hy
    simp [below,hz]
  have Hdrop := potential_drop hl (ranks_update_mono W a b) hbelow
    (by positivity : (0:ℝ) ≤ 1/(16*(D+1)*q))
  have hc' : ((below (ranks (update W a b)) l).card : ℝ) + (H \ B).card ≤
      (below (ranks W) l).card := by exact_mod_cast hcard
  have Hdrop' := Hdrop (by
    rw [one_div_mul_eq_div]
    linarith : ((below (ranks (update W a b)) l).card : ℝ) ≤
      (below (ranks W) l).card - 1/(16*(D+1)*q)*(below (ranks W) l).card)
  convert Hdrop' using 1; field_simp; ring

omit [FiniteDimensional K V] in
theorem chosenLevel_spec (W : State (K:=K) (V:=V))
    (b : Points (K:=K) (V:=V)) :
    chosenLevel W b ≤ ranks W b ∧
    ∀ j ≤ ranks W b, (level (ranks W) j).card ≤ (level (ranks W) (chosenLevel W b)).card := by
  have h := Classical.choose_spec ((range (ranks W b + 1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0, by simp⟩)
  simpa only [chosenLevel, mem_range, Nat.lt_succ_iff] using h

theorem scan_potential_bound (q : ℝ) (hq : 0 < q)
    (W : State (K:=K) (V:=V)) (fs : List (Module.Dual K V × Points (K:=K) (V:=V))) :
    ((scan q W fs).1:ℝ) / (32*(Module.finrank K V+1)*q) ≤
      potential (Module.finrank K V) (ranks W) -
        potential (Module.finrank K V) (ranks (scan q W fs).2) := by
  induction fs generalizing W with
  | nil => simp [scan]
  | cons f fs ih =>
    by_cases he : IsExpensive W q f
    · simp only [scan, ite_eq_left he]
      have hL := chosenLevel_spec W f.2
      have hD : chosenLevel W f.2 ≤ Module.finrank K V :=
        hL.1.trans (Submodule.finrank_le _)
      have hd := expensive_drop W hq hD
        (fun j hj => hL.2 _ (hj.trans hL.1)) f.1 f.2 he.1 he.2
      have hi := ih (update W f.1 f.2)
      push_cast
      rw [add_div]
      linarith
    · simpa only [scan, ite_eq_right he] using ih W

theorem scan_expensive_bound (q : ℝ) (hq : 0 < q)
    (W : State (K:=K) (V:=V)) (fs : List (Module.Dual K V × Points (K:=K) (V:=V))) :
    ((scan q W fs).1:ℝ) ≤
      32*(Module.finrank K V+1)^2*q*Real.log (Fintype.card (Points (K:=K) (V:=V))+1 : ℝ) := by
  have h := scan_potential_bound q hq W fs
  have hn := potential_nonneg (Module.finrank K V) (ranks (scan q W fs).2)
  have hu := potential_le (Module.finrank K V) (ranks W)
  have hden : (0:ℝ) < 32*(Module.finrank K V+1)*q := by positivity
  have h' : ((scan q W fs).1:ℝ)/(32*(Module.finrank K V+1)*q) ≤
      (Module.finrank K V+1)*Real.log (Fintype.card (Points (K:=K) (V:=V))+1 : ℝ) := by
    linarith
  have h'' := (div_le_iff₀ hden).mp h'
  convert h'' using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end State
end SharpLogRamsey.Marking

namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem joint_bound_of_product {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    (hprod : (S.card:ℝ)*T.card ≤ 16*(Nat.card K:ℝ)^(n+3)) :
    (incidenceCount S T:ℝ) ≤ 20*(Nat.card K:ℝ)^(n+2) := by
  let q : ℝ := Nat.card K
  let p : ℝ := (∑ i ∈ range (n+2), q^i)/(∑ i ∈ range (n+3), q^i)
  let a : ℝ := (S.card:ℝ)*T.card
  have hq : 0 < q := by
    change (0:ℝ) < Nat.card K
    have h := (Finite.one_lt_card : 1 < Nat.card K)
    exact_mod_cast (lt_trans Nat.zero_lt_one h)
  have hv : 0 < ∑ i ∈ range (n+3), q^i := by
    apply sum_pos' (fun i hi => pow_nonneg hq.le _)
    exact ⟨0, by simp, by simp⟩
  have hp : p ≤ 1/q := by
    apply (div_le_div_iff₀ hv hq).mpr
    have he : (∑ i ∈ range (n+3), q^i) = q*(∑ i ∈ range (n+2), q^i)+1 := geom_sum_succ
    linarith
  have ha : 0 ≤ a := by positivity
  have hm := mul_le_mul_of_nonneg_right hp ha
  have hcap : p*a ≤ 16*q^(n+2) := by
    have hd : a/q ≤ 16*q^(n+2) := by
      apply (div_le_iff₀ hq).mpr
      have he : q^(n+3) = q^(n+2)*q := by rw [← pow_succ]
      change a ≤ 16*q^(n+3) at hprod
      rw [he] at hprod
      nlinarith
    have he : (1/q)*a = a/q := by ring
    rw [he] at hm
    exact hm.trans hd
  have hs := projective_mixing_sq hdim S T
  change ((incidenceCount S T:ℝ)-p*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hs
  simp only [mul_assoc] at hs
  change ((incidenceCount S T:ℝ)-p*a)^2 ≤ q^(n+1)*a at hs
  have hmul := mul_le_mul_of_nonneg_left hprod (pow_nonneg hq.le (n+1))
  have he : q^(n+1)*(16*q^(n+3)) = (4*q^(n+2))^2 := by
    rw [mul_left_comm, ← pow_add, mul_pow, ← pow_mul]
    congr 1 <;> ring
  change q^(n+1)*a ≤ q^(n+1)*(16*q^(n+3)) at hmul
  rw [he] at hmul
  have hfour : 0 ≤ 4*q^(n+2) := by positivity
  have habs := (sq_le_sq₀ (abs_nonneg ((incidenceCount S T:ℝ)-p*a)) hfour).mp
    (by simpa using hs.trans hmul)
  have hdev := le_abs_self ((incidenceCount S T:ℝ)-p*a)
  linarith

theorem poor_joint_domain_bound {n : ℕ} (hdim : Module.finrank K V = n+3)
    (W : State (K:=K) (V:=V)) {l r : ℕ}
    (hmax : (level (ranks W) r).card ≤ (level (ranks W) l).card) :
    (incidenceCount (level (ranks W) r) (poorDomain W l):ℝ) ≤
      20*(Nat.card K:ℝ)^(n+2) := by
  apply joint_bound_of_product hdim
  calc
    _ ≤ ((level (ranks W) l).card:ℝ)*(poorDomain W l).card :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmax) (by positivity)
    _ ≤ _ := poor_marginal_product hdim W l

end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_Popular
attribute [-instance] _root_.OAI.SharpLogRamsey.flagFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem popular_joint_card {d l r : ℕ} (hdim : Module.finrank K V = d+1)
    (W : State (K:=K) (V:=V)) (hl : l ≤ r) (hr : r ≤ d)
    (hZ : (level (ranks W) l).Nonempty) :
    ((popularJoint W l r).card:ℝ) ≤ 64*(Nat.card K:ℝ)^d := by
  cases l with
  | zero => simp [popularJoint, popular_zero W hZ]
  | succ l =>
    let q : ℝ := Nat.card K
    have hq : 1 ≤ q := by
      change (1:ℝ) ≤ Nat.card K
      exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K).le
    have hc : ((popularJoint W (l+1) r).card:ℝ) ≤
        ((popularDomain W (l+1)).card:ℝ)*(2*q^(d-r)) := by
      calc
        _ ≤ ∑ b ∈ popularDomain W (l+1),
            ((if ranks W b = r then (partnerDomain (W b)).image (Prod.mk b) else ∅).card:ℝ) := by
          exact_mod_cast (card_biUnion_le (s := popularDomain W (l+1))
            (t := fun b => if ranks W b = r then (partnerDomain (W b)).image (Prod.mk b) else ∅))
        _ ≤ ∑ _b ∈ popularDomain W (l+1), 2*q^(d-r) := by
          apply sum_le_sum
          intro b hb
          split_ifs with h
          · rw [card_image_of_injective _ (by intro x y hxy; exact Prod.mk.inj hxy |>.2)]
            exact partner_card hdim (W b) h hr
          · simp; positivity
        _ = _ := by simp
    have hpop := popular_card W l hZ
    have hh := hc.trans (mul_le_mul_of_nonneg_right hpop (show 0 ≤ 2*q^(d-r) by positivity))
    have hp : q^(l+1+(d-r)) ≤ q^d := pow_le_pow_right₀ hq (by omega)
    calc
      _ ≤ (32*q^(l+1))*(2*q^(d-r)) := hh
      _ = 64*q^(l+1+(d-r)) := by rw [pow_add]; ring
      _ ≤ 64*q^d := mul_le_mul_of_nonneg_left hp (by norm_num)

end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] in
lemma chosenLevel_from_rank (W : State (K:=K) (V:=V)) (b : Points (K:=K) (V:=V)) :
    chosenLevel W b = levelFromRank W (ranks W b) := rfl

omit [FiniteDimensional K V] in
lemma flagKind_expensive (q : ℝ) (W : State (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) :
    flagKind q W f = .expensive ↔ IsExpensive W q f := by
  unfold flagKind IsExpensive
  split_ifs <;> simp_all

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma rankMask_card : Fintype.card (RankMask (K:=K) (V:=V)) =
    (Module.finrank K V+1)*3 := by
  rw [Fintype.card_prod,Fintype.card_fin]
  rfl

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in

lemma update_annihilates_later (W : State (K:=K) (V:=V))
    (f g : ScanFlag (K:=K) (V:=V)) (hW : W g.2 ≤ LinearMap.ker g.1)
    (hfg : f.1 g.2.rep = 0 → g.1 f.2.rep = 0) :
    update W f.1 f.2 g.2 ≤ LinearMap.ker g.1 := by
  unfold update
  split_ifs with h
  · apply sup_le hW
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
    exact hfg h
  · exact hW

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset SharpLogRamsey.Incidence
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma incidentPairs_card (S : Finset (Points (K:=K) (V:=V)))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    (incidentPairs S T).card = incidenceCount S T := by
  simp only [incidentPairs,incidenceCount,card_eq_sum_ones,sum_filter,sum_product]
  rw [sum_comm]

omit [Finite K] in
lemma cheapDomain_membership (W : State (K:=K) (V:=V)) (f : ProjectivePair (K:=K) (V:=V))
    (hf : _root_.OAI.SharpLogRamsey.Incidence.Incident f.1 f.2) (hW : W f.1 ≤ LinearMap.ker f.2.rep)
    (hc : ¬IsExpensive W (Nat.card K) (f.2.rep,f.1)) :
    f ∈ projectiveCheapDomain W (maskAt (Nat.card K) W (f.2.rep,f.1)) := by
  have hr : ranks W f.1 < Module.finrank K V := by
    have hle := Submodule.finrank_mono hW
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero f.2.rep_nonzero
    unfold ranks
    omega
  dsimp only [projectiveCheapDomain,maskAt]
  rw [ite_eq_left hr]
  unfold flagKind
  split_ifs with hp hpoor
  · apply mem_biUnion.mpr
    refine ⟨f.1,?_,?_⟩
    · simpa only [popularDomain,mem_filter,mem_univ,true_and,chosenLevel_from_rank] using hp
    · rw [ite_eq_left rfl]
      apply mem_image.mpr
      exact ⟨f.2,by simpa only [partnerDomain,mem_filter,mem_univ,true_and] using hW,rfl⟩
  · apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_,?_⟩,hf⟩
    · simp [level]
    · simpa only [poorDomain,mem_filter,mem_univ,true_and,chosenLevel_from_rank] using hpoor
  · exact False.elim (hc ⟨hp,hpoor⟩)

omit [Finite K] [FiniteDimensional K V] in
lemma popularJoint_empty_of_level_empty (W : State (K:=K) (V:=V)) (l r : ℕ)
    (he : level (ranks W) r = ∅) : popularJoint W l r = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨b,hb,hf⟩ := mem_biUnion.mp hf
  by_cases hr : ranks W b = r
  · have hm : b ∈ level (ranks W) r := by simp [level,hr]
    rw [he] at hm
    exact notMem_empty _ hm
  · simp only [ite_eq_right hr,notMem_empty] at hf

theorem projectiveCheapDomain_card {n : ℕ} (hdim : Module.finrank K V = n+3)
    (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) :
    ((projectiveCheapDomain W m).card:ℝ) ≤ 64*(Nat.card K:ℝ)^(n+2) := by
  unfold projectiveCheapDomain
  split_ifs with hr
  · have hs := levelFromRank_spec W m.1.val
    have hrd : m.1.val ≤ n+2 := by omega
    cases hk : m.2 with
    | expensive => simp
    | poor =>
      rw [incidentPairs_card]
      exact (poor_joint_domain_bound hdim W (hs.2 _ le_rfl)).trans (by
        have hq : 0 ≤ (Nat.card K:ℝ)^(n+2) := by positivity
        nlinarith)
    | popular =>
      by_cases he : level (ranks W) m.1.val = ∅
      · rw [popularJoint_empty_of_level_empty W _ _ he]
        simp
      · have hne : (level (ranks W) (levelFromRank W m.1.val)).Nonempty := by
          apply card_pos.mp
          exact (card_pos.mpr (nonempty_iff_ne_empty.mpr he)).trans_le (hs.2 _ le_rfl)
        exact popular_joint_card (by omega) W hs.1 hrd hne
  · simp

end
end SharpLogRamsey.Marking

namespace SharpLogRamsey.Marking
open ProjectiveDuality
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem backwardScan_consistent {N : ℕ} (F : Fin N → Flag K V) (hF : Consistent F) :
    ScanConsistent (backwardScan F) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact hF j.rev i.rev (Fin.rev_lt_rev.mpr hij)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_FlagConstruction
attribute [-instance] _root_.OAI.SharpLogRamsey.flagFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey

section LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem flag_vectors_independent {m : ℕ} (a : Fin m → V)
    (b : Fin m → Module.Dual K V)
    (ha : ∀ i, a i ≠ 0)
    (hz : ∀ i j, i ≤ j → b j (a i) = 0)
    (hn : ∀ i j, i < j → b i (a j) ≠ 0) :
    LinearIndependent K a := by
  induction m with
  | zero => exact linearIndependent_empty_type
  | succ m ih =>
    apply linearIndependent_finSucc'.mpr
    refine ⟨ih (Fin.init a) (Fin.init b) (fun i => ha i.castSucc)
      (fun i j h => hz i.castSucc j.castSucc h)
      (fun i j h => hn i.castSucc j.castSucc h), ?_⟩
    cases m with
    | zero => simpa using ha (Fin.last 0)
    | succ n =>
      intro hmem
      let j : Fin (n + 1 + 1) := (Fin.last n).castSucc
      have hspan : Submodule.span K (Set.range (Fin.init a)) ≤
          LinearMap.ker (b j) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact hz i.castSucc j (by simpa [j] using Fin.le_last i)
      have hzero : b j (a (Fin.last (n + 1))) = 0 := hspan hmem
      exact hn j (Fin.last (n + 1)) (by simp [j]) hzero

theorem flag_length_lt_finrank [FiniteDimensional K V] {m : ℕ}
    (a : Fin (m+1) → V) (b : Fin (m+1) → Module.Dual K V)
    (ha : ∀ i, a i ≠ 0) (hb : b (Fin.last m) ≠ 0)
    (hz : ∀ i j, i ≤ j → b j (a i) = 0)
    (hn : ∀ i j, i < j → b i (a j) ≠ 0) :
    m + 1 < Module.finrank K V := by
  let W := LinearMap.ker (b (Fin.last m))
  let a' : Fin (m+1) → W := fun i => ⟨a i, hz i (Fin.last m) (Fin.le_last i)⟩
  have hli : LinearIndependent K a' :=
    LinearIndependent.of_comp W.subtype (flag_vectors_independent a b ha hz hn)
  have hle : m + 1 ≤ Module.finrank K W := by
    simpa using hli.fintype_card_le_finrank
  have hproper : W ≠ ⊤ := by
    exact fun h => hb (LinearMap.ker_eq_top.mp h)
  exact hle.trans_lt (Submodule.finrank_lt hproper)

end LinearAlgebra

section Flags
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

variable {K V}

theorem flagGraph_cliqueFree [FiniteDimensional K V] {d N : ℕ}
    (hdim : Module.finrank K V = d+1) (F : Fin N → Flag K V) :
    (flagGraph K V F).CliqueFree (d+1) := by
  intro S hS
  let e := S.orderEmbOfFin hS.card_eq
  let a : Fin (d+1) → V := fun i => (F (e i)).point.rep
  let b : Fin (d+1) → Module.Dual K V := fun i => (F (e i)).dualPoint.rep
  have hedge (i j : Fin (d+1)) (h : i < j) :
      Incident K V (F (e i)).point (F (e j)).dualPoint ∧
      ¬ Incident K V (F (e j)).point (F (e i)).dualPoint := by
    apply (flagGraph_adj_of_lt F (e.strictMono h)).mp
    exact hS.isClique (S.orderEmbOfFin_mem hS.card_eq i)
      (S.orderEmbOfFin_mem hS.card_eq j) (ne_of_lt (e.strictMono h))
  have hz : ∀ i j, i ≤ j → b j (a i) = 0 := by
    intro i j h
    rcases lt_or_eq_of_le h with hlt | rfl
    · exact (hedge i j hlt).1
    · exact (F (e i)).incident
  have hn : ∀ i j, i < j → b i (a j) ≠ 0 := by
    intro i j h
    exact (hedge i j h).2
  have hlt := flag_length_lt_finrank a b (fun i => (F (e i)).point.rep_nonzero)
    (F (e (Fin.last d))).dualPoint.rep_nonzero hz hn
  omega

theorem prime_flagGraph_cliqueFree (q d N : ℕ) [Fact q.Prime]
    (F : Fin N → Flag (ZMod q) (Fin (d+1) → ZMod q)) :
    (flagGraph (ZMod q) (Fin (d+1) → ZMod q) F).CliqueFree (d+1) := by
  apply flagGraph_cliqueFree
  simp

end Flags
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype ι]

lemma entropy_cond_tuple_domains (p : Law Ω) (C : Ω → Γ) (F : Ω → ι → α)
    (S : Γ → ι → Finset α)
    (hS : ∀ x, p.mass x ≠ 0 → ∀ i, F x i ∈ S (C x) i)
    (c : Γ) (hc : (p.map C).mass c ≠ 0) :
    entropy ((p.cond C c).map F) ≤ ∑ i, Real.log (S c i).card := by
  apply (entropy_subadditive_pi _).trans
  apply sum_le_sum
  intro i hi
  change entropy (((p.cond C c).map F).map (fun x => x i)) ≤ _
  rw [Law.map_map]
  apply entropy_mapped_support
  intro x hx
  obtain ⟨hp,he⟩ := p.cond_support C c hc x hx
  simpa only [Function.comp_apply,he] using hS x hp i

lemma entropy_context_bound (p : Law Ω) (C : Ω → Γ) (F : Ω → α) (J : Γ → ℝ)
    (hJ : ∀ c, (p.map C).mass c ≠ 0 → entropy ((p.cond C c).map F) ≤ J c) :
    entropy (p.map F) ≤ entropy (p.map C)+∑ c, (p.map C).mass c*J c := by
  have hf : (p.map (fun x => (F x,C x))).fst = p.map F := by
    rw [← Law.map_fst,Law.map_map]
    rfl
  have hh := entropy_map_le (p.map (fun x => (F x,C x))) Prod.fst
  rw [Law.map_fst,hf,entropy_cond_chain p C F] at hh
  apply hh.trans
  apply add_le_add le_rfl
  apply sum_le_sum
  intro a ha
  by_cases hc : (p.map C).mass a = 0
  · simp [hc]
  · exact mul_le_mul_of_nonneg_left (hJ a hc) ((p.map C).nonneg a)

lemma entropy_adjoin_mask {M : Type*} [Fintype M] (p : Law Ω)
    (C : Ω → Γ) (mask : Ω → M) :
    entropy (p.map (fun x => (C x,mask x))) ≤
      entropy (p.map C)+Real.log (Fintype.card M) := by
  have hf : (p.map (fun x => (C x,mask x))).fst = p.map C := by
    rw [← Law.map_fst,Law.map_map]; rfl
  have hs : (p.map (fun x => (C x,mask x))).snd = p.map mask := by
    rw [← Law.map_snd,Law.map_map]; rfl
  have hm := entropy_le_log_card (p.map mask) univ (by simp)
  have ht := entropy_subadditive (p.map (fun x => (C x,mask x)))
  rw [hf,hs] at ht
  exact ht.trans (add_le_add le_rfl (by simpa only [card_univ] using hm))

omit [Fintype α] [Fintype ι] in
lemma maskedValues_mem (E : Finset ι) (f : ι → α) (D : ι → Finset α)
    (hD : ∀ i, f i ∈ D i) (i : ι) : maskedValues E f i ∈ maskedDomains E D i := by
  by_cases hi : i ∈ E
  · simp only [maskedValues,maskedDomains,ite_eq_left hi]
    exact mem_image.mpr ⟨f i,hD i,rfl⟩
  · simp [maskedValues,maskedDomains,hi]

omit [Fintype α] [Fintype ι] in
lemma maskedDomains_log_card (E : Finset ι) (D : ι → Finset α) (i : ι) :
    Real.log (maskedDomains E D i).card = if i ∈ E then Real.log (D i).card else 0 := by
  by_cases hi : i ∈ E
  · simp [maskedDomains,hi,card_image_of_injective (D i) (Option.some_injective α)]
  · simp [maskedDomains,hi]

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ M ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι]

theorem marking_message_entropy (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α) (D : Γ → ι → Finset α) (J : ℝ)
    (hD : ∀ x, p.mass x ≠ 0 → ∀ i, F x i ∈ D (C x) i)
    (hJ : ∀ c i, Real.log (D c i).card ≤ J) :
    entropy (p.map (markingMessage C mask E F)) ≤ entropy (p.map C)+
      Real.log (Fintype.card M)+(∑ x, p.mass x*((E (mask x)).card:ℝ))*J := by
  let G := fun x => (C x,mask x)
  let T := fun x => maskedValues (E (mask x)) (F x)
  have hG := entropy_adjoin_mask p C mask
  have hcond (c : Γ × M) (hc : (p.map G).mass c ≠ 0) :
      entropy ((p.cond G c).map T) ≤ (E c.2).card*J := by
    let S := fun c : Γ × M => maskedDomains (E c.2) (D c.1)
    have hh := entropy_cond_tuple_domains p G T S (fun x hx i =>
      maskedValues_mem _ _ _ (hD x hx) i) c hc
    apply hh.trans
    simp only [S,maskedDomains_log_card]
    calc
      _ ≤ ∑ i, if i ∈ E c.2 then J else 0 := by
        apply sum_le_sum
        intro i hi
        split_ifs
        · exact hJ c.1 i
        · exact le_rfl
      _ = _ := by simp
  have hsum : ∑ c, (p.map G).mass c*((E c.2).card:ℝ)*J =
      (∑ x, p.mass x*((E (mask x)).card:ℝ))*J := by
    rw [← sum_mul, p.sum_map G (fun c => ((E c.2).card:ℝ))]
  change entropy (p.map (fun x => (T x,G x))) ≤ _
  rw [entropy_cond_chain p G T]
  calc
    _ ≤ (entropy (p.map C)+Real.log (Fintype.card M))+
        ∑ c, (p.map G).mass c*((E c.2).card*J) := by
      apply add_le_add hG
      apply sum_le_sum
      intro c hc
      by_cases hn : (p.map G).mass c = 0
      · simp [hn]
      · exact mul_le_mul_of_nonneg_left (hcond c hn) ((p.map G).nonneg c)
    _ = _ := by simp_rw [← mul_assoc]; rw [hsum]

omit [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι] in
lemma markingDecodedDomains_mem (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α)
    (x : Ω)
    (hcheap : ∀ i, i ∉ E (mask x) → F x i ∈ cheap (markingMessage C mask E F x) i)
    (i : ι) : F x i ∈ markingDecodedDomains E cheap (markingMessage C mask E F x) i := by
  by_cases hi : i ∈ E (mask x)
  · simp [markingDecodedDomains,markingMessage,maskedValues,hi]
  · change F x i ∈ if i ∈ E (mask x) then _ else _
    rw [ite_eq_right hi]
    exact hcheap i hi

omit [Fintype α] [Fintype Γ] [Fintype M] in
lemma markingDecodedDomains_entropy (E : M → Finset ι)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (J : ℝ)
    (hJ : ∀ θ i, i ∉ E θ.2.2 → Real.log (cheap θ i).card ≤ J)
    (θ : (ι → Option α) × (Γ × M)) :
    (∑ i, Real.log (markingDecodedDomains E cheap θ i).card) ≤
      ((Fintype.card ι:ℝ)-(E θ.2.2).card)*J := by
  have h (i : ι) : Real.log (markingDecodedDomains E cheap θ i).card ≤
      if i ∈ E θ.2.2 then 0 else J := by
    by_cases hi : i ∈ E θ.2.2
    · simp only [markingDecodedDomains,ite_eq_left hi]
      cases θ.1 i <;> simp
    · simpa only [markingDecodedDomains,ite_eq_right hi] using hJ θ i hi
  have he : (∑ i, if i ∈ E θ.2.2 then (0:ℝ) else J) =
      ((Fintype.card ι:ℝ)-(E θ.2.2).card)*J := by
    rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    have hcard : (univ.filter (fun i => i ∉ E θ.2.2)).card = Fintype.card ι-(E θ.2.2).card := by
      rw [← sdiff_eq_filter,card_sdiff_of_subset (subset_univ _),card_univ]
    rw [hcard,Nat.cast_sub (card_le_univ _)]
  exact (sum_le_sum (fun i _ => h i)).trans_eq he

theorem marking_entropy_upper (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α) (D : Γ → ι → Finset α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (Jprev J₀ : ℝ)
    (hD : ∀ x, p.mass x ≠ 0 → ∀ i, F x i ∈ D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card ≤ Jprev)
    (hc : ∀ x, p.mass x ≠ 0 → ∀ i, i ∉ E (mask x) →
      F x i ∈ cheap (markingMessage C mask E F x) i)
    (hcheap : ∀ θ i, i ∉ E θ.2.2 → Real.log (cheap θ i).card ≤ J₀) :
    entropy (p.map F) ≤ entropy (p.map C)+Real.log (Fintype.card M)+
      Fintype.card ι*J₀+(∑ x, p.mass x*((E (mask x)).card:ℝ))*(Jprev-J₀) := by
  let θ := markingMessage C mask E F
  have hu := entropy_context_bound p θ F
    (fun z => ((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀) (fun z hz =>
      (entropy_cond_tuple_domains p θ F (markingDecodedDomains E cheap)
        (fun x hx i => markingDecodedDomains_mem C mask E F cheap x (hc x hx) i) z hz).trans
          (markingDecodedDomains_entropy E cheap J₀ hcheap z))
  have hm := marking_message_entropy p C mask E F D Jprev hD hprev
  have he : (∑ z, (p.map θ).mass z * (((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀)) =
      ((Fintype.card ι:ℝ)-∑ x, p.mass x*((E (mask x)).card:ℝ))*J₀ := by
    rw [p.sum_map θ]
    change (∑ x, p.mass x * (((Fintype.card ι:ℝ)-(E (mask x)).card)*J₀)) = _
    simp_rw [← mul_assoc,mul_sub]
    rw [← sum_mul,sum_sub_distrib,← sum_mul,p.total,one_mul]
  rw [he] at hu
  dsimp only [θ] at hu
  linarith

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma pairCode_count (q : ℝ) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V))) :
    ((pairCode q W fs).filter (fun z => z.1.2=.expensive)).length =
      (scan q W (fs.map toScan)).1 := by
  induction fs generalizing W with
  | nil => rfl
  | cons f fs ih =>
    by_cases h : IsExpensive W q (toScan f)
    · simp [pairCode,maskAt,flagKind_expensive,scan,h,pairStep,replayStep,ih]
    · simp [pairCode,maskAt,flagKind_expensive,scan,h,pairStep,replayStep,ih]

lemma pairCode_spec (q : ℝ) (hq : q=(Nat.card K:ℝ)) (W : State (K:=K) (V:=V))
    (fs : List (ProjectivePair (K:=K) (V:=V)))
    (hcons : ScanConsistent (fs.map toScan))
    (hinc : ∀ f∈fs, Incidence.Incident f.1 f.2)
    (hW : ∀ f∈fs, W f.1 ≤ LinearMap.ker f.2.rep) (n : ℕ) (hn : n<fs.length) :
    let cs := pairCode q W fs
    let z := cs[n]'(by rw [pairCode_length]; exact hn)
    let Wn := pairReplay W ((cs.map Prod.snd).take n)
    z.2=(if z.1.2=.expensive then some fs[n] else none) ∧
      (z.1.2≠.expensive → fs[n]∈projectiveCheapDomain Wn z.1) := by
  induction fs generalizing W n with
  | nil => simp at hn
  | cons f fs ih =>
    have hp := List.pairwise_cons.mp hcons
    cases n with
    | zero =>
      simp only [pairCode,List.getElem_cons_zero,List.take_zero,pairReplay,maskAt]
      constructor
      · simp only [flagKind_expensive]
      · intro hc
        have he : ¬IsExpensive W q (toScan f) :=
          fun he => hc ((flagKind_expensive q W (toScan f)).mpr he)
        have he' : ¬IsExpensive W (Nat.card K) (f.2.rep,f.1) := by
          simpa only [←hq,toScan] using he
        simpa only [←hq,maskAt,toScan] using
          cheapDomain_membership W f (hinc f (by simp)) (hW f (by simp)) he'
    | succ n =>
      let s := if IsExpensive W q (toScan f) then some f else none
      have HW (g : ProjectivePair (K:=K) (V:=V)) (hg : g∈fs) :
          pairStep W s g.1 ≤ LinearMap.ker g.2.rep := by
        have hw := hW g (by simp [hg])
        by_cases he : IsExpensive W q (toScan f)
        · simp only [s,ite_eq_left he,pairStep,Option.map_some,replayStep]
          apply update_annihilates_later W (toScan f) (toScan g) hw
          exact hp.1 _ (List.mem_map.mpr ⟨g,hg,rfl⟩)
        · simpa only [s,ite_eq_right he,pairStep,Option.map_none,replayStep] using hw
      have hh := ih (pairStep W s) hp.2 (fun g hg => hinc g (by simp [hg])) HW n (by simpa using hn)
      exact hh

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma mem_expensiveMask {N : ℕ} (M : Fin N → RankMask (K:=K) (V:=V)) (i : Fin N) :
    i∈expensiveMask M ↔ (M i).2=.expensive := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma ofFn_codeTuple {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    List.ofFn (codeTuple q F) = pairCode q (fun _ => ⊥) (List.ofFn F) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,pairCode_length]
  · intro i h1 h2
    simp only [List.getElem_ofFn,codeTuple]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma expensiveMask_card {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    (expensiveMask (tupleMask q F)).card =
    (scan q (fun _ => ⊥) ((List.ofFn F).map toScan)).1 := by
  have hfilter (xs : List (RankMask (K:=K) (V:=V) × Option (ProjectivePair (K:=K) (V:=V)))) :
      (xs.filter (fun a => a.1.2=.expensive)).length =
        (xs.map (fun a => if a.1.2=.expensive then 1 else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => by_cases h : a.1.2=.expensive <;> simp [h,ih,Nat.add_comm]
  rw [←pairCode_count,←ofFn_codeTuple,hfilter, List.map_ofFn,List.sum_ofFn]
  rw [expensiveMask,Finset.card_filter]
  rfl

lemma tuple_sent_eq {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hcons : ScanConsistent ((List.ofFn F).map toScan))
    (hinc : ∀ i, Incidence.Incident (F i).1 (F i).2) (i : Fin N) :
    (codeTuple (Nat.card K) F i).2 =
      Selection.maskedValues (expensiveMask (tupleMask (Nat.card K) F)) F i := by
  have hh := pairCode_spec (Nat.card K) rfl (fun _ => ⊥) (List.ofFn F) hcons
    (by intro f hf; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf; exact hinc j)
    (fun _ _ => bot_le) i.val (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [Selection.maskedValues,mem_expensiveMask,tupleMask,codeTuple,List.getElem_ofFn] using hh.1

lemma cheapTuple_mem {Γ : Type*} {N : ℕ} (c : Γ)
    (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hcons : ScanConsistent ((List.ofFn F).map toScan))
    (hinc : ∀ i, Incidence.Incident (F i).1 (F i).2) (i : Fin N)
    (hi : i∉expensiveMask (tupleMask (Nat.card K) F)) :
    F i∈cheapTuple (Selection.maskedValues (expensiveMask (tupleMask (Nat.card K) F)) F,
      (c,tupleMask (Nat.card K) F)) i := by
  have hs : List.ofFn (Selection.maskedValues (expensiveMask (tupleMask (Nat.card K) F)) F) =
      (pairCode (Nat.card K) (fun _ => ⊥) (List.ofFn F)).map Prod.snd := by
    rw [←ofFn_codeTuple,List.map_ofFn]
    exact congrArg List.ofFn (funext (fun j => (tuple_sent_eq F hcons hinc j).symm))
  have hh := pairCode_spec (Nat.card K) rfl (fun _ => ⊥) (List.ofFn F) hcons
    (by intro f hf; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf; exact hinc j)
    (fun _ _ => bot_le) i.val (by simpa only [List.length_ofFn] using i.isLt)
  have hc : (codeTuple (Nat.card K) F i).1.2≠.expensive := by
    exact fun hc => hi ((mem_expensiveMask _ _).mpr hc)
  simp only [cheapTuple,hs,tupleMask]
  simpa only [codeTuple,List.getElem_ofFn] using hh.2 hc

variable [Finite K]
lemma cheapTuple_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (θ : (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V)))) (i : Fin N) :
    ((cheapTuple θ i).card:ℝ) ≤ 64*(Nat.card K:ℝ)^(n+2) :=
  projectiveCheapDomain_card hdim _ _

lemma cheapTuple_log_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (θ : (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V)))) (i : Fin N) :
    Real.log (cheapTuple θ i).card ≤ Real.log (64*(Nat.card K:ℝ)^(n+2)) := by
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
  by_cases hz : (cheapTuple θ i).card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    exact Real.log_nonneg (by nlinarith [(one_le_pow₀ hq : (1:ℝ)≤(Nat.card K:ℝ)^(n+2))])
  · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hz)) (cheapTuple_card hdim θ i)

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem actual_entropy_upper {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω → Γ) (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V))
    (D : Γ → Fin N → Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x, p.mass x≠0 → ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x, p.mass x≠0 → ∀ i, Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x, p.mass x≠0 → ∀ i, F x i∈D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card≤Jprev) :
    Selection.entropy (p.map F) ≤ Selection.entropy (p.map C)+
      N*Real.log ((Module.finrank K V+1)*3:ℝ)+
      N*Real.log (64*(Nat.card K:ℝ)^(n+2))+
      (∑ x, p.mass x*((expensiveMask (tupleMask (Nat.card K) (F x))).card:ℝ))*
        (Jprev-Real.log (64*(Nat.card K:ℝ)^(n+2))) := by
  have hh := Selection.marking_entropy_upper p C (fun x => tupleMask (Nat.card K) (F x))
    expensiveMask F D cheapTuple Jprev (Real.log (64*(Nat.card K:ℝ)^(n+2))) hD hprev
    (fun x hx i hi => cheapTuple_mem (C x) (F x) (hcons x hx) (hinc x hx) i hi)
    (fun θ i _ => cheapTuple_log_card hdim θ i)
  convert hh using 1 <;>
    try simp only [Fintype.card_fun,Fintype.card_fin,rankMask_card,Nat.cast_pow,Real.log_pow,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  congr 2 <;> exact Subsingleton.elim _ _

omit [Fintype (Projectivization K (Module.Dual K V))] in

lemma expected_expensive_bound {N : ℕ} (p : Selection.Law Ω)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) :
    (∑ x, p.mass x*((expensiveMask (tupleMask (Nat.card K) (F x))).card:ℝ)) ≤
      32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
        Real.log (Fintype.card (Points (K:=K) (V:=V))+1:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).trans' Nat.zero_lt_one
  calc
    _ ≤ ∑ x, p.mass x*(32*(Module.finrank K V+1)^2*(Nat.card K:ℝ)*
        Real.log (Fintype.card (Points (K:=K) (V:=V))+1:ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      rw [expensiveMask_card]
      exact mul_le_mul_of_nonneg_left (scan_expensive_bound _ hq _ _) (p.nonneg x)
    _ = _ := by rw [← Finset.sum_mul,p.total,one_mul]

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_FinalMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

variable [FiniteDimensional K V] [Finite K]
lemma actualFlag_card {d : ℕ} (hdim : Module.finrank K V=d+1) :
    Fintype.card (Flag K V) =
      (∑ i ∈ range (d+1),Nat.card K^i)*(∑ i ∈ range d,Nat.card K^i) := by
  let e : Flag K V ≃ Σ b : Projectivization K (Module.Dual K V),
      {a : Projectivization K V // Incidence.Incident a b} :=
    { toFun := fun f=>⟨f.dualPoint,f.point,f.incident⟩
      invFun := fun f=>⟨f.2.1,f.1,f.2.2⟩
      left_inv := fun f=>by cases f; rfl
      right_inv := fun f=>by cases f; rfl }
  rw [←Nat.card_eq_fintype_card,Nat.card_congr e,Nat.card_sigma]
  simp_rw [Incidence.card_incident_points hdim]
  simp only [sum_const,card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K (Module.Dual K V)
    (Subspace.dual_finrank_eq.trans hdim)]

end
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_SelectionLogBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Real
open scoped Classical
noncomputable section

theorem log_choose_bound {N ℓ : ℕ} (hℓ : 0<ℓ) (hN : ℓ≤N) :
    log (N.choose ℓ:ℝ)≤(ℓ:ℝ)*(1+log (N:ℝ)-log (ℓ:ℝ)) := by
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hn : (0:ℝ)<N := by exact_mod_cast hℓ.trans_le hN
  have hf : (0:ℝ)<ℓ.factorial := by exact_mod_cast Nat.factorial_pos ℓ
  have he := Real.pow_div_factorial_le_exp (ℓ:ℝ) hl.le ℓ
  have hp : (0:ℝ)<(ℓ:ℝ)^ℓ := pow_pos hl _
  have hfac : (ℓ:ℝ)^ℓ/exp ℓ≤(ℓ.factorial:ℝ) := by
    apply (div_le_iff₀ (exp_pos _)).mpr
    have h := (div_le_iff₀ hf).mp he
    nlinarith
  have hc := (Nat.choose_le_pow_div ℓ N : (N.choose ℓ:ℝ)≤(N:ℝ)^ℓ/ℓ.factorial)
  have hc' : (N.choose ℓ:ℝ)≤exp ℓ*((N:ℝ)/(ℓ:ℝ))^ℓ := by
    calc
      _ ≤ (N:ℝ)^ℓ/ℓ.factorial := hc
      _ ≤ (N:ℝ)^ℓ/((ℓ:ℝ)^ℓ/exp ℓ) :=
        div_le_div_of_nonneg_left (pow_nonneg hn.le _) (div_pos hp (exp_pos _)) hfac
      _ = exp ℓ*((N:ℝ)/(ℓ:ℝ))^ℓ := by rw [div_pow]; field_simp
  have hcpos : (0:ℝ)<N.choose ℓ := by exact_mod_cast Nat.choose_pos hN
  have H := log_le_log hcpos hc'
  rw [log_mul (ne_of_gt (exp_pos _)) (ne_of_gt (pow_pos (div_pos hn hl) _)),
    log_exp,log_pow,log_div (ne_of_gt hn) (ne_of_gt hl)] at H
  nlinarith

variable {α : Type*} [Fintype α] [Nonempty α]

theorem selected_entropy_log_bound {N ℓ : ℕ} (hℓ : 0<ℓ) (hN : ℓ≤N)
    (p : Law ((Fin N→α)×(Fin ℓ→α))) (reverse : (Fin ℓ→α)→(Fin ℓ→α))
    {C : ℝ} (hC : 0<C)
    (hdom : ∀ g,p.fst.mass g≤C/(Fintype.card α:ℝ)^N)
    (hselect : ∀ g f,p.mass (g,f)≠0→Occurs f g ∨ Occurs (reverse f) g) :
    (ℓ:ℝ)*(log (Fintype.card α:ℝ)-1-log (N:ℝ)+log (ℓ:ℝ))-log (2*C)≤
      entropy p.snd := by
  have H := selected_entropy_bound hN p reverse hC hdom hselect
  have hc := log_choose_bound hℓ hN
  have hp : (0:ℝ)<N.choose ℓ := by exact_mod_cast Nat.choose_pos hN
  rw [log_mul (ne_of_gt (by positivity : (0:ℝ)<2*C)) (ne_of_gt hp)] at H
  nlinarith

theorem selected_entropy_source_scales {N ℓ d : ℕ} (hd : 1≤d)
    (hℓ : 0<ℓ) (hN : ℓ≤N)
    (p : Law ((Fin N→α)×(Fin ℓ→α))) (reverse : (Fin ℓ→α)→(Fin ℓ→α))
    {C q σ η c : ℝ} (hC : 0<C) (hq : 0<q) (hσ : 0<σ) (hc : 0 < c)
    (hdom : ∀ g,p.fst.mass g≤C/(Fintype.card α:ℝ)^N)
    (hselect : ∀ g f,p.mass (g,f)≠0→Occurs f g ∨ Occurs (reverse f) g)
    (hsize : (N:ℝ)≤q^d*σ) (hlength : c*q*σ^(1+η)≤(ℓ:ℝ))
    (halphabet : q^(2*d-1)≤(Fintype.card α:ℝ)) :
    (ℓ:ℝ)*((d:ℝ)*log q+η*log σ+log c-1)-log (2*C)≤entropy p.snd := by
  have hn : (0:ℝ)<N := by exact_mod_cast hℓ.trans_le hN
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hlN := log_le_log hn hsize
  rw [log_mul (ne_of_gt (pow_pos hq _)) (ne_of_gt hσ),log_pow] at hlN
  have hlL := log_le_log (by positivity : 0 < c*q*σ^(1+η)) hlength
  rw [log_mul (by positivity : c*q≠0) (ne_of_gt (rpow_pos_of_pos hσ _)),
    log_mul (ne_of_gt hc) (ne_of_gt hq),log_rpow hσ] at hlL
  have hlA := log_le_log (pow_pos hq (2*d-1)) halphabet
  rw [log_pow] at hlA
  have has : ((2*d-1:ℕ):ℝ)=2*(d:ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  rw [has] at hlA
  have hpoint : (d:ℝ)*log q+η*log σ+log c-1≤
      log (Fintype.card α:ℝ)-1-log (N:ℝ)+log (ℓ:ℝ) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hpoint hl.le
  exact (sub_le_sub_right hh _).trans
    (selected_entropy_log_bound hℓ hN p reverse hC hdom hselect)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_SelectedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Real Finset
open scoped Classical
noncomputable section
variable {Ω α : Type} [Fintype Ω] [Fintype α] [Nonempty α]

theorem selected_map_entropy {N ℓ d : ℕ} (hd : 1 ≤ d) (hℓ : 0 < ℓ) (hN : ℓ ≤ N)
    (p : Law Ω) (stream : Ω → Fin N → α) (F : Ω → Fin ℓ → α)
    (reverse : (Fin ℓ → α) → (Fin ℓ → α))
    {C q σ η c : ℝ} (hC : 0 < C) (hq : 0 < q) (hσ : 0 < σ) (hc : 0 < c)
    (hdom : ∀ g, (p.map stream).mass g ≤ C/(Fintype.card α:ℝ)^N)
    (hselect : ∀ x, p.mass x ≠ 0 → Occurs (F x) (stream x) ∨ Occurs (reverse (F x)) (stream x))
    (hsize : (N:ℝ) ≤ q^d*σ) (hlength : c*q*σ^(1+η) ≤ (ℓ:ℝ))
    (halphabet : q^(2*d-1) ≤ (Fintype.card α:ℝ)) :
    (ℓ:ℝ)*((d:ℝ)*log q+η*log σ+log c-1)-log (2*C) ≤ entropy (p.map F) := by
  let P := p.map (fun x => (stream x,F x))
  have hfst : P.fst = p.map stream := by
    rw [←Law.map_fst]
    dsimp only [P]
    rw [Law.map_map]
    rfl
  have hsnd : P.snd = p.map F := by
    rw [←Law.map_snd]
    dsimp only [P]
    rw [Law.map_map]
    rfl
  have hh := selected_entropy_source_scales hd hℓ hN P reverse hC hq hσ hc
    (by simpa only [hfst] using hdom) (by
      intro g f hgf
      obtain ⟨x,hx,he⟩ := p.map_support (fun x => (stream x,F x)) (g,f) hgf
      have hh := hselect x hx
      have he1 : stream x = g := congrArg Prod.fst he
      have he2 : F x = f := congrArg Prod.snd he
      simpa only [he1,he2] using hh) hsize hlength halphabet
  rwa [hsnd] at hh

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_OrderedClassLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

omit [FiniteDimensional K V] in

lemma scanConsistent_ordered {N m : ℕ}
    (F : Fin N→ProjectivePair (K:=K) (V:=V))
    (hF : ScanConsistent ((List.ofFn F).map toScan)) (e : Fin m ↪o Fin N) :
    ScanConsistent ((List.ofFn (fun i=>F (e i))).map toScan) := by
  unfold ScanConsistent at hF ⊢
  rw [List.map_ofFn] at hF ⊢
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact List.pairwise_ofFn.mp hF (e.strictMono hij)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TailSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K] in
lemma geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

end
end SharpLogRamsey.HighRankExcess
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]

lemma Law.onEvent_mean_le_two (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→ℝ) (hf : ∀ x,0≤f x) :
    ∑ x : E,(p.onEvent E (by linarith)).mass x*f x≤2*∑ x,p.mass x*f x := by
  rw [p.onEvent_mean]
  apply (div_le_iff₀ (by linarith : 0<p.event E)).mpr
  have hn : 0≤∑ x,p.mass x*f x := sum_nonneg (fun x _=>mul_nonneg (p.nonneg x) (hf x))
  calc
    _ ≤ ∑ x,p.mass x*f x := sum_le_univ_sum_of_nonneg (fun x=>mul_nonneg (p.nonneg x) (hf x))
    _ ≤ _ := by nlinarith

lemma Law.onEvent_map_le_two (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→Y) (y : Y) :
    ((p.onEvent E (by linarith)).map (fun x : E=>f x)).mass y≤2*(p.map f).mass y := by
  have hh:=p.onEvent_mean_le_two E hE (fun x=>if f x=y then 1 else 0) (by intro x; split_ifs <;> positivity)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using hh

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_HighRankEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section
variable {K V Ω : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype Ω]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_bound {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (Fintype.card (Projectivization K V):ℝ)≤2*(Nat.card K:ℝ)^d := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  simp only [Nat.cast_pow]
  exact HighRankExcess.geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)) d

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TrackedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α β Ω : Type} [Fintype α] [Fintype β] [Fintype Ω]

omit [Fintype α] in
lemma occurs_iff_orderEmbedding {N n : ℕ} (f : Fin n→α) (g : Fin N→α) :
    Occurs f g ↔ ∃ e : Fin n↪o Fin N,∀ i,g (e i)=f i := by
  constructor
  · rintro ⟨S,hS⟩
    exact ⟨S.val.orderEmbOfFin S.property,hS⟩
  · rintro ⟨e,he⟩
    let S : Finset (Fin N):=univ.image e
    have hS : S.card=n:=by rw [card_image_of_injective _ e.injective,card_univ,Fintype.card_fin]
    refine ⟨⟨S,hS⟩,?_⟩
    have hh : e=S.orderEmbOfFin hS:=orderEmbOfFin_unique' hS (fun i=>mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    intro i
    change g (S.orderEmbOfFin hS i)=f i
    simpa only [←hh] using he i

omit [Fintype α] in
lemma occurs_restrict {N n m : ℕ} {f : Fin n→α} {g : Fin N→α}
    (e : Fin m↪o Fin n) (h : Occurs f g) : Occurs (fun i=>f (e i)) g := by
  obtain ⟨j,hj⟩:=(occurs_iff_orderEmbedding _ _).mp h
  exact (occurs_iff_orderEmbedding _ _).mpr ⟨e.trans j,fun i=>hj (e i)⟩

omit [Fintype α] in
lemma occurs_reverse_restrict {N n m : ℕ} {f : Fin n→α} {g : Fin N→α}
    (e : Fin m↪o Fin n) (h : Occurs (reverseTuple f) g) :
    Occurs (reverseTuple (fun i=>f (e i))) g := by
  let er : Fin m↪o Fin n:=OrderEmbedding.ofStrictMono (fun i=>(e i.rev).rev) (by
    intro i j hij
    exact Fin.rev_lt_rev.mpr (e.strictMono (Fin.rev_lt_rev.mpr hij)))
  have hh:=occurs_restrict er h
  change Occurs (fun i=>f (Fin.rev ((e i.rev).rev))) g at hh
  change Occurs (fun i=>f (e i.rev)) g
  simpa only [Fin.rev_rev] using hh

variable {N n m : ℕ} {p : Law Ω} {G : Ω→Fin n→β} {B C L : ℝ}

lemma ContextOutput.map_domination (e : ContextOutput p G m B C L)
    (stream : Ω→Fin N→α) {D : ℝ} (hL : 0 ≤ L)
    (hdom : ∀ g,(p.map stream).mass g ≤ D/(Fintype.card α:ℝ)^N) :
    ∀ g,(e.μ.map (stream∘e.source)).mass g ≤ L*D/(Fintype.card α:ℝ)^N := by
  intro g
  rw [←Law.map_map]
  calc
    _ ≤ ∑ x ∈ univ.filter (fun x=>stream x=g),L*p.mass x:=by
      dsimp only [Law.map]
      convert sum_le_sum (fun x (_ : x∈univ.filter (fun x=>stream x=g))=>e.dominated x) using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    _ = L*(p.map stream).mass g:=by
      simp only [Law.map,mul_sum]
      congr!
    _ ≤ L*(D/(Fintype.card α:ℝ)^N):=mul_le_mul_of_nonneg_left (hdom g) hL
    _ = _:=by ring

lemma ContextOutput.length_le (e : ContextOutput p G m B C L) : m ≤ n := by
  have hx : Nonempty e.X:=by
    by_contra hh
    have hz : Fintype.card e.X=0:=Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hh)
    have : IsEmpty e.X:=Fintype.card_eq_zero_iff.mp hz
    have he : (0:ℝ)=1:=by simpa using e.μ.total
    norm_num at he
  obtain ⟨x⟩:=hx
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (e.chosen x) (e.chosen x).injective

theorem ContextOutput.tracked_entropy [Nonempty α]
    (e : ContextOutput p G m B C L) (stream : Ω→Fin N→α) (F : Ω→Fin n→α)
    (φ : α→β) (hφ : Function.Injective φ) (hG : ∀ x i,G x i=φ (F x i))
    {d : ℕ} (hd : 1 ≤ d) (hm : 0 < m) (hn : n ≤ N)
    {D q σ η c : ℝ} (hD : 0 < D) (hL : 0 < L) (hq : 0 < q) (hσ : 0 < σ) (hc : 0 < c)
    (hdom : ∀ g,(p.map stream).mass g ≤ D/(Fintype.card α:ℝ)^N)
    (hselect : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x))
    (hsize : (N:ℝ) ≤ q^d*σ) (hlength : c*q*σ^(1+η) ≤ m)
    (halphabet : q^(2*d-1) ≤ (Fintype.card α:ℝ)) :
    (m:ℝ)*((d:ℝ)*log q+η*log σ+log c-1)-log (2*(L*D)) ≤
      entropy (e.μ.map (fun x i=>G (e.source x) (e.chosen x i))) := by
  let f:=fun x i=>F (e.source x) (e.chosen x i)
  have hselection : ∀ x,e.μ.mass x≠0→Occurs (f x) (stream (e.source x)) ∨
      Occurs (reverseTuple (f x)) (stream (e.source x)):=by
    intro x _
    rcases hselect (e.source x) (e.supported x) with h|h
    · exact Or.inl (occurs_restrict (e.chosen x) h)
    · exact Or.inr (occurs_reverse_restrict (e.chosen x) h)
  have hh:=selected_map_entropy hd hm (e.length_le.trans hn) e.μ (stream∘e.source) f reverseTuple
    (mul_pos hL hD) hq hσ hc (e.map_domination stream hL.le hdom) hselection hsize hlength halphabet
  have he : entropy (e.μ.map (fun x i=>G (e.source x) (e.chosen x i)))=entropy (e.μ.map f) := by
    have hp : Function.Injective (fun a : Fin m→α=>φ∘a):=by
      intro a b hab
      funext i
      exact hφ (congrFun hab i)
    have h:=entropy_map_eq_of_injective (e.μ.map f) (fun a : Fin m→α=>φ∘a) hp
    rw [Law.map_map] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    funext x i
    exact hG _ _
  rwa [he]
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RootCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real ActualHighRank ExecutedPotential TreeDecoder
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] in
lemma projective_log_card_add_one {d : ℕ} (hdim : Module.finrank K V=d+1)
    (hσ : 1≤log (Nat.card K:ℝ)) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤((d:ℝ)+2)*log (Nat.card K:ℝ) := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hq0 : (0:ℝ)<Nat.card K := by linarith
  have hc:=projective_card_bound hdim
  have hp : 1≤(Nat.card K:ℝ)^d:=one_le_pow₀ hq
  have hlog : log (3:ℝ)≤2 := by
    have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  calc
    _ ≤ log (3*(Nat.card K:ℝ)^d) := log_le_log (by positivity) (by nlinarith)
    _ = log 3+(d:ℝ)*log (Nat.card K:ℝ) := by
      rw [log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow]
    _ ≤ _ := by nlinarith

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_CostContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_monomial_le_power (C a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x^b := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-b)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-b))*x^b := by rw [mul_assoc, ←rpow_add hx0]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hx.le (rpow_nonneg hx0.le _)

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_SelectedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
lemma classCount_pos (i : ℕ) : 0 < classCount i:=by unfold classCount;positivity

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TrackedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Marking
open scoped Classical BigOperators
noncomputable section
variable {Ω α : Type} [Fintype Ω] [Fintype α] {n m : ℕ}
  {p : Law Ω} {G : Ω→Fin n→α} {B C L : ℝ}

lemma ContextOutput.log_size (e : ContextOutput p G m B C L) {J : ℝ}
    (hJ : 0 ≤ J) (hB : B ≤ exp J) : ∀ z i,log (e.domains z i).card ≤ J := by
  intro z i
  by_cases hz : (e.domains z i).card=0
  · simpa only [hz,Nat.cast_zero,log_zero] using hJ
  · have hp : (0:ℝ) < (e.domains z i).card:=by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (log_le_log hp ((e.size z i).trans hB)).trans_eq (log_exp _)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_InitialTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey
open Finset Real Selection Marking
open scoped Classical BigOperators
noncomputable section

namespace Selection
variable {α : Type} [Fintype α] [Nonempty α]

lemma uniformLaw_conditioned {E : Finset α} (hE : (1:ℝ)/2 ≤ FiniteStreamTail.probability E) :
    ∀ a,((uniformLaw.onEvent E (by rw [uniformLaw_event];linarith)).map (Subtype.val : E→α)).mass a ≤
      2/(Fintype.card α:ℝ) := by
  intro a
  have hh:=uniformLaw.onEvent_map_le_two E (by rwa [uniformLaw_event]) id a
  rw [Law.map_id] at hh
  convert hh using 1 <;> simp [uniformLaw]
  ring
end Selection

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

lemma rectangle_pair_iff [Finite K] [FiniteDimensional K V] (W : Submodule K V) (f : Flag K V) :
    (flagPair f).swap∈orthogonalRectangle Projectivization.rep Projectivization.rep W ↔
      f∈RectangleStreamEvent.rectangle W := by
  simp only [orthogonalRectangle,mem_filter,mem_univ,true_and,RectangleStreamEvent.rectangle,
    InitialRectangles.IsRectangle,Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
  rfl

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma selected_reverse_consistent {N k : ℕ} (z : Fin N→Flag K V)
    (e : Fin k↪o Fin N) (hc : Consistent (fun j=>z (e j))) :
    ScanConsistent ((List.ofFn (fun j=>flagPair (z (e j.rev)))).map toScan) := by
  have hh:=backwardScan_consistent (fun j=>z (e j)) hc
  simpa only [backwardScan,List.map_ofFn,Function.comp_def,flagPair,toScan] using hh
end
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_InitialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.InitialExperiment
open Finset Real Filter Selection Marking FiniteStreamTail RectangleStreamEvent
open scoped Classical BigOperators Topology
noncomputable section

lemma occupancyConstant_pos (i : ℕ) : 0 < occupancyConstant i:=by
  unfold occupancyConstant
  exact div_pos (by positivity) (log_pos (by norm_num))

variable (i q : ℕ) [Fact q.Prime] (N k : ℕ)

attribute [local instance] OAI.SharpLogRamsey.InitialExperiment.initLawProjective
attribute [local instance] OAI.SharpLogRamsey.InitialExperiment.initLawDualProjective
attribute [local instance] OAI.SharpLogRamsey.InitialExperiment.initLawFlagNonempty
lemma law_dom (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ)) :
    ∀ g,((law i q N hN).map (Subtype.val : goodEvent i q N→_)).mass g ≤
      2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N := by
  intro g
  have hh:=uniformLaw_conditioned (goodEvent_half i q N hN) g
  convert hh using 1 <;> simp only [law,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]

variable (h : ∀ z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q),
  k ≤ (flagGraph (ZMod q) (Fin (i+4)→ZMod q) z).indepNum)

lemma chosen_consistent (z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q)) :
    Consistent (fun j=>z (chosen i q N k h z j)):=Classical.choose_spec (independent_selected z (h z))

lemma tuple_occurs (z : goodEvent i q N) : Occurs (reverseTuple (tuple i q N k h z)) z.val := by
  apply (occurs_iff_orderEmbedding _ _).mpr
  refine ⟨chosen i q N k h z.val,?_⟩
  intro j
  simp only [reverseTuple,tuple,Fin.rev_rev]

lemma tuple_consistent (z : goodEvent i q N) :
    ScanConsistent ((List.ofFn (fun j=>flagPair (tuple i q N k h z j))).map toScan) :=
  selected_reverse_consistent z.val (chosen i q N k h z.val) (chosen_consistent i q N k h z.val)

lemma tuple_occupancy (z : goodEvent i q N) :
    ∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j : Fin k=>(flagPair (tuple i q N k h z j)).swap∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤
          occupancyConstant i*log (q:ℝ) := by
  intro W
  let e : Fin k↪Fin N:= (Equiv.toEmbedding (Equiv.ofBijective Fin.rev (by
    constructor
    · intro a b hab;simpa using congrArg Fin.rev hab
    · intro a;exact ⟨a.rev,by simp⟩))).trans (chosen i q N k h z.val).toEmbedding
  have hh:=hits_embedding (rectangle W) z.val e
  have hz : (hits (rectangle W) z.val:ℝ)<occupancyConstant i*log (q:ℝ):=(mem_filter.mp z.property).2 W
  apply le_trans _ hz.le
  convert (Nat.cast_le (α:=ℝ)).mpr hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply congrArg Finset.card
  ext j
  simp only [mem_filter,mem_univ,true_and,rectangle_pair_iff]
  rfl

lemma alphabet_cap {P : ℝ} (hP : 4 ≤ P) (σ : ℝ) (he : exp σ=(q:ℝ)) :
    (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ) ≤
      P*(q:ℝ)^(i+3)*exp (((i+2:ℕ):ℝ)*σ) := by
  have hq : 2 ≤ q:=(Fact.out : q.Prime).two_le
  have hh : Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)) ≤ 4*q^(i+3)*q^(i+2):=by
    rw [actualFlag_card (d:=i+3) (by simp),Nat.card_zmod]
    have h1:=InitialRectangles.sum_powers_le_two hq (show 0 < i+3+1 by omega)
    have h2:=InitialRectangles.sum_powers_le_two hq (show 0 < i+3 by omega)
    have hx:=Nat.mul_le_mul h1 h2
    simp only [Nat.add_sub_cancel,show i+3-1=i+2 by omega] at hx
    exact hx.trans_eq (by ring)
  rw [exp_nat_mul,he]
  have hh' : (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ) ≤ 4*(q:ℝ)^(i+3)*(q:ℝ)^(i+2):=by exact_mod_cast hh
  apply hh'.trans
  gcongr
end
end SharpLogRamsey.InitialExperiment

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TrackedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.trackProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.trackDualProjective
lemma flag_alphabet_lower (i q : ℕ) [Fact q.Prime] :
    (q:ℝ)^(2*(i+3)-1) ≤ (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ) := by
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+3)+1:=by simp
  have halphabet : (q:ℝ)^(2*(i+3)-1) ≤ (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ):=by
    have hh : q^(2*(i+3)-1) ≤ Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):=by
      rw [actualFlag_card hdim,Nat.card_zmod]
      have h1 : q^(i+3) ≤ ∑ j∈range ((i+3)+1),q^j:=single_le_sum (by intros;positivity) (mem_range.mpr (by omega))
      have h2 : q^(i+2) ≤ ∑ j∈range (i+3),q^j:=single_le_sum (by intros;positivity) (mem_range.mpr (by omega))
      calc
        _ = q^(i+3)*q^(i+2):=by rw [←pow_add];congr 1;omega
        _ ≤ _:=Nat.mul_le_mul h1 h2
    exact_mod_cast hh
  exact halphabet

lemma tracked_log_budget (i q : ℕ) (σ Δ P : ℝ) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ)
    (hP : 1 ≤ P) (he : exp σ=(q:ℝ)) :
    0 ≤ log P+((i+3:ℕ):ℝ)*σ+Δ ∧
    P*(q:ℝ)^(i+3)*exp Δ ≤ exp (log P+((i+3:ℕ):ℝ)*σ+Δ) ∧
    log P+((i+3:ℕ):ℝ)*σ+Δ-jointJ (ZMod q) (i+3) ≤ Δ+(|log P|+|log 64|) := by
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hP0 : 0 < P:=lt_of_lt_of_le zero_lt_one hP
  have hlogq : log (q:ℝ)=σ:=by rw [←he,log_exp]
  refine ⟨by have:=log_nonneg hP;positivity,?_,?_⟩
  · rw [exp_add,exp_add,exp_log hP0,exp_nat_mul,he]
  · dsimp only [jointJ]
    rw [Nat.card_zmod,log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow,hlogq]
    linarith [le_abs_self (log P),neg_abs_le (log 64)]

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_ParameterIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ParameterIteration
open Real

theorem finite_contraction (D : ℕ→ℝ) (a b R : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hb' : b≤1/2) (h₀ : D 0≤R) (T : ℕ)
    (hstep : ∀ i<T,D (i+1)≤a+b*D i) :
    D T≤2*a+b^T*R := by
  have hbound : ∀ i≤T,D i≤2*a+b^i*R := by
    intro i
    induction i with
    | zero => intro _; simpa only [pow_zero,one_mul] using h₀.trans (by linarith)
    | succ i ih =>
      intro hi
      have hd := ih (by omega)
      have hh := (hstep i (by omega)).trans (add_le_add_right (mul_le_mul_of_nonneg_left hd hb) a)
      have hac : a+2*a*b≤2*a := by nlinarith
      rw [pow_succ]
      nlinarith
  exact hbound T le_rfl

theorem source_contraction {σ β η : ℝ} (hσ : 1≤σ) (hβ : 0≤β)
    (hhalf : σ^(-η/4)≤1/2) (D : ℕ→ℝ) (T : ℕ)
    (hT : 1≤(T:ℝ)*η/4) (h₀ : D 0≤σ)
    (hstep : ∀ i<T,D (i+1)≤σ^(2*β)+D i*σ^(-η/4)) :
    D T≤3*σ^(2*β) := by
  have hσ0 : 0<σ := lt_of_lt_of_le zero_lt_one hσ
  have ha : 1≤σ^(2*β) := one_le_rpow hσ (by positivity)
  have Hb := finite_contraction D (σ^(2*β)) (σ^(-η/4)) σ
    (rpow_nonneg hσ0.le _) (rpow_nonneg hσ0.le _) hhalf h₀ T (by
      intro i hi
      simpa only [mul_comm] using hstep i hi)
  have hpow : (σ^(-η/4))^T*σ=σ^(1-(T:ℝ)*η/4) := by
    rw [←rpow_natCast,←rpow_mul hσ0.le]
    conv_lhs => rhs; rw [←rpow_one σ]
    rw [←rpow_add hσ0]
    congr 1
    ring
  rw [hpow] at Hb
  have hsmall : σ^(1-(T:ℝ)*η/4)≤1 := rpow_le_one_of_one_le_of_nonpos hσ (by linarith)
  linarith

theorem eventual_half {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in Filter.atTop, σ^(-η/4)≤1/2 := by
  have ht : Filter.Tendsto (fun σ : ℝ=>σ^(-η/4)) Filter.atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (show 0<η/4 by linarith))
  exact ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2))

theorem prescribed_count {η : ℝ} (hη : 0<η) :
    1≤(⌈8/η⌉₊:ℝ)*η/4 := by
  have h := Nat.le_ceil (8/η)
  have hh := mul_le_mul_of_nonneg_right h hη.le
  have he : (8/η)*η=(8:ℝ) := div_mul_cancel₀ 8 (ne_of_gt hη)
  rw [he] at hh
  linarith

end SharpLogRamsey.ParameterIteration

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_IterationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma evenScale_bounds {σ η : ℝ} (hσ : 0 ≤ σ) :
    σ^beta η ≤ (evenScale σ η:ℝ) ∧
    (evenScale σ η:ℝ) ≤ 2*σ^beta η+2 ∧ Even (evenScale σ η) := by
  have hp : 0 ≤ σ^beta η:=rpow_nonneg hσ _
  have hlo:=Nat.le_ceil (σ^beta η/2)
  have hup:=Nat.ceil_lt_add_one (show 0 ≤ σ^beta η/2 by positivity)
  refine ⟨?_,?_,?_⟩
  · dsimp only [evenScale];push_cast;linarith
  · dsimp only [evenScale];push_cast;linarith
  · exact even_two_mul _

lemma stage_next {σ η D : ℝ} {k : ℕ} (hk : 0 < k) :
    stageD σ η k (D*σ^(-η/3)*k) (16*scaleKstar σ η D)=nextD σ η D := by
  have hk0 : (k:ℝ)≠0:=by exact_mod_cast hk.ne'
  dsimp only [stageD,nextD,scaleKstar]
  rw [mul_div_cancel_right₀ _ hk0]
  ring

lemma nextD_lower {σ η D : ℝ} (hσ : 0 ≤ σ) (hD : 0 ≤ D) :
    σ^beta η ≤ nextD σ η D := by
  unfold nextD
  have hp : 0 ≤ σ^beta η:=rpow_nonneg hσ _
  have h1 : 0 ≤ D*σ^(-η/3):=by positivity
  have h2 : 0 ≤ 16*D*σ^(6*beta η)*σ^(-η):=by positivity
  nlinarith

theorem eventually_iteration_scales (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, 0 ≤ D →
      nextD σ η D ≤ σ^(2*beta η)+D*σ^(-η/4) ∧
      (D ≤ σ^(1-η/2) → nextD σ η D ≤ σ^(1-η/2)) := by
  have hg1 : beta η-η/3 < -η/4:=by unfold beta;linarith
  have hg2 : 7*beta η-η < -η/4:=by unfold beta;linarith
  have hg3 : 2*beta η < 1-η/2:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power 1 (beta η-η/3) (-η/4) (1/2) hg1 (by norm_num),
    eventually_monomial_le_power 16 (7*beta η-η) (-η/4) (1/2) hg2 (by norm_num),
    eventually_monomial_le_power 1 (2*beta η) (1-η/2) (1/2) hg3 (by norm_num),
    eventually_monomial_le_power 1 (1-3*η/4) (1-η/2) (1/2) (by linarith) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ h1 h2 h3 h4 hσ D hD
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hp : σ^beta η ≤ σ^(2*beta η):=rpow_le_rpow_of_exponent_le hσ (by have:=beta_pos hη;linarith)
  have heq : nextD σ η D=σ^beta η+D*σ^(beta η-η/3)+16*D*σ^(7*beta η-η) := by
    unfold nextD
    rw [mul_add,mul_add]
    simp only [mul_one]
    have hP1 : σ^beta η*σ^(-η/3)=σ^(beta η-η/3):=by rw [←rpow_add hσ0];congr 1;ring
    have hP2 : σ^beta η*σ^(6*beta η)*σ^(-η)=σ^(7*beta η-η):=by
      rw [←rpow_add hσ0,←rpow_add hσ0];congr 1;ring
    calc
      _ = σ^beta η+D*(σ^beta η*σ^(-η/3))+16*D*(σ^beta η*σ^(6*beta η)*σ^(-η)):=by ring
      _ = _:=by rw [hP1,hP2]
  have hrec : nextD σ η D ≤ σ^(2*beta η)+D*σ^(-η/4):=by
    rw [heq]
    have hh1:=mul_le_mul_of_nonneg_left h1 hD
    have hh2:=mul_le_mul_of_nonneg_left h2 hD
    nlinarith only [hp,hh1,hh2]
  refine ⟨hrec,?_⟩
  intro hDu
  have hu : D*σ^(-η/4) ≤ σ^(1-3*η/4):=by
    calc
      _ ≤ σ^(1-η/2)*σ^(-η/4):=mul_le_mul_of_nonneg_right hDu (rpow_nonneg hσ0.le _)
      _ = _:=by rw [←rpow_add hσ0];congr 1;ring
  linarith

theorem eventually_initial_stage (d : ℕ) (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ k : ℕ,
      Admissible σ η (stageD σ η k 0 (((d-1:ℕ):ℝ)*σ)) (evenScale σ η) ∧
      stageD σ η k 0 (((d-1:ℕ):ℝ)*σ) ≤ σ := by
  have hg1 : beta η < 1-η/2:=by unfold beta;linarith
  have hg2 : 1-η+beta η < 1-η/2:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power 1 (beta η) (1-η/2) (1/2) hg1 (by norm_num),
    eventually_monomial_le_power ((d-1:ℕ):ℝ) (1-η+beta η) (1-η/2) (1/2) hg2 (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ h1 h2 hσ k
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hh : stageD σ η k 0 (((d-1:ℕ):ℝ)*σ)=σ^beta η+((d-1:ℕ):ℝ)*σ^(1-η+beta η):=by
    unfold stageD
    simp only [zero_div,add_zero]
    rw [mul_add,mul_one]
    congr 1
    calc
      _ = ((d-1:ℕ):ℝ)*(σ^beta η*σ^(1:ℝ)*σ^(-η)):=by rw [rpow_one];ring
      _ = _:=by rw [←rpow_add hσ0,←rpow_add hσ0];congr 2;ring
  have hu : stageD σ η k 0 (((d-1:ℕ):ℝ)*σ) ≤ σ^(1-η/2):=by rw [hh];linarith
  obtain ⟨hRl,hRu,hRe⟩:=evenScale_bounds (η:=η) hσ0.le
  refine ⟨⟨?_,hu,hRl,hRu,hRe⟩,hu.trans ?_⟩
  · rw [hh];have : 0 ≤ ((d-1:ℕ):ℝ)*σ^(1-η+beta η):=by positivity
    linarith
  · calc
      _ ≤ σ^(1:ℝ):=rpow_le_rpow_of_exponent_le hσ (by linarith)
      _ = _:=rpow_one _
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_NumericalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma iterationD_succ (d : ℕ) (σ η : ℝ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    iterationD d σ η k (n+1)=nextD σ η (iterationD d σ η k n) := by
  exact stage_next hk

lemma iteration_data {d k : ℕ} {σ η : ℝ} (hk : 0 < k) (hσ : 1 ≤ σ)
    (hinit : Admissible σ η (iterationD d σ η k 0) (evenScale σ η))
    (hiter : ∀ D : ℝ,0 ≤ D→nextD σ η D ≤ σ^(2*beta η)+D*σ^(-η/4) ∧
      (D ≤ σ^(1-η/2)→nextD σ η D ≤ σ^(1-η/2))) :
    ∀ n, 0 ≤ (iterationBudgets d σ η k n).1 ∧ 0 ≤ (iterationBudgets d σ η k n).2 ∧
      Admissible σ η (iterationD d σ η k n) (evenScale σ η) := by
  have hσ0 : 0 ≤ σ:=by linarith
  intro n
  induction n with
  | zero => exact ⟨le_refl 0,mul_nonneg (Nat.cast_nonneg _) hσ0,hinit⟩
  | succ n ih =>
    have hD : 0 ≤ iterationD d σ η k n:=(rpow_nonneg hσ0 _).trans ih.2.2.1
    obtain ⟨hlo,hup,hev⟩:=evenScale_bounds (η:=η) hσ0
    refine ⟨?_,?_,?_⟩
    · change 0 ≤ iterationD d σ η k n*σ^(-η/3)*(k:ℝ)
      positivity
    · change 0 ≤ 16*scaleKstar σ η (iterationD d σ η k n)
      unfold scaleKstar;positivity
    · rw [iterationD_succ d σ η hk]
      exact ⟨nextD_lower hσ0 hD,(hiter _ hD).2 ih.2.2.D_upper,hlo,hup,hev⟩

theorem eventually_iteration_budgets (d : ℕ) (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ k : ℕ,0 < k→
      (∀ n,0 ≤ (iterationBudgets d σ η k n).1 ∧ 0 ≤ (iterationBudgets d σ η k n).2 ∧
        Admissible σ η (iterationD d σ η k n) (evenScale σ η)) ∧
      (iterationBudgets d σ η k (⌈8/η⌉₊+1)).1 ≤ k ∧
      (iterationBudgets d σ η k (⌈8/η⌉₊+1)).2 ≤ 48*σ^(8*beta η) := by
  have hg : 2*beta η-η/3 < 0:=by unfold beta;linarith
  filter_upwards [eventually_initial_stage d η hη hηu,eventually_iteration_scales η hη hηu,
    ParameterIteration.eventual_half hη,
    eventually_monomial_le_power 3 (2*beta η-η/3) 0 1 hg (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ hinit hiter hhalf hsmall hσ k hk
  have hσ0 : 0 < σ:=by linarith
  have hdata:=iteration_data hk hσ (hinit k).1 hiter
  let T:=⌈8/η⌉₊
  have hD : iterationD d σ η k T ≤ 3*σ^(2*beta η):=by
    apply ParameterIteration.source_contraction hσ (beta_pos hη).le hhalf _ T
      (ParameterIteration.prescribed_count hη) (hinit k).2
    intro n _
    rw [iterationD_succ d σ η hk]
    exact (hiter _ ((rpow_nonneg hσ0.le _).trans (hdata n).2.2.1)).1
  refine ⟨hdata,?_,?_⟩
  · change iterationD d σ η k T*σ^(-η/3)*(k:ℝ) ≤ k
    have hh : iterationD d σ η k T*σ^(-η/3) ≤ 1:=by
      calc
        _ ≤ 3*σ^(2*beta η)*σ^(-η/3):=mul_le_mul_of_nonneg_right hD (rpow_nonneg hσ0.le _)
        _ = 3*σ^(2*beta η-η/3):=by rw [mul_assoc,←rpow_add hσ0];congr 2;ring
        _ ≤ 1:=by simpa using hsmall
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg k)
  · change 16*scaleKstar σ η (iterationD d σ η k T) ≤ _
    unfold scaleKstar
    calc
      _ ≤ 16*(3*σ^(2*beta η))*σ^(6*beta η):=by
        have hh:=mul_le_mul_of_nonneg_right hD (rpow_nonneg hσ0.le (6*beta η))
        have hh':=mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 16)
        simpa only [mul_assoc] using hh'
      _ = _:=by rw [show 16*(3*σ^(2*beta η))*σ^(6*beta η)=48*(σ^(2*beta η)*σ^(6*beta η)) by ring,←rpow_add hσ0];congr 2;ring
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_FiniteIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

lemma retained_length {r Q k m : ℝ} {n T : ℕ} (hr : 1 ≤ r) (hQ : 0 ≤ Q)
    (hn : n ≤ T) (hk : Q/2 ≤ k) (hm : k/r^n ≤ m) :
    ((1/2)/r^T)*Q ≤ m := by
  have hr0 : 0 < r:=by linarith
  calc
    _ = (Q/2)/r^T:=by ring
    _ ≤ (Q/2)/r^n:=div_le_div_of_nonneg_left (by positivity)
      (pow_pos hr0 _) (pow_le_pow_right₀ hr hn)
    _ ≤ k/r^n:=div_le_div_of_nonneg_right hk (by positivity)
    _ ≤ _:=hm

attribute [local instance] OAI.SharpLogRamsey.Marking.finiteIterProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.finiteIterDualProjective
theorem eventually_iterated_context (i : ℕ) (η P M0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hP : 1 ≤ P)
    (hPs : stepPrefactor (i+3) ≤ P) (hM0 : 0 ≤ M0) :
    let T:=⌈8/η⌉₊+1
    let r:ℝ:=256*classCount i
    let Lstar:ℝ:=(4*classCount i)^T
    let c:ℝ:=(1/2)/r^T
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω : Type) [Fintype Ω] (N k : ℕ) (p : Law Ω)
      (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q)),
      0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) → ((q:ℝ)*σ^(1+η))/2 ≤ k →
      (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
      (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
      (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
      ContextOutput p (fun x j=>flagPair (F x j)) k
        (P*(q:ℝ)^(i+3)*exp (((i+2:ℕ):ℝ)*σ)) 0 1 →
      ∃ m : ℕ,c*(q:ℝ)*σ^(1+η) ≤ m ∧
        Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m
          (P*(q:ℝ)^(i+3)*exp (48*σ^(8*beta η))) k Lstar) := by
  intro T r Lstar c
  have hK : 0 < classCount i:=classCount_pos i
  have hr : 1 ≤ r:=by
    dsimp [r]
    have : (1:ℝ) ≤ classCount i:=by exact_mod_cast hK
    linarith
  have hr0 : 0 < r:=by linarith
  have hLone : (1:ℝ) ≤ 4*classCount i:=by
    have : (1:ℝ) ≤ classCount i:=by exact_mod_cast hK
    linarith
  have hLs : 0 < Lstar:=by dsimp [Lstar];positivity
  have hc : 0 < c:=by dsimp [c];positivity
  filter_upwards [eventually_tracked_step i η c Lstar P M0 hη hηu hc hLs hP hPs hM0,
    eventually_iteration_budgets (i+3) η hη hηu,eventually_ge_atTop (1:ℝ)] with σ hstep hbud hσ
  intro q _ hq he Ω _ N k p stream F hk hkn hku hklo hdom hselect hN hcon hocc e0
  obtain ⟨hdata,hΛlast,hΔlast⟩:=hbud k hk
  have hσ0 : 0 < σ:=by linarith
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hh : ∀ n ≤ T, ∃ m : ℕ,(k:ℝ)/r^n ≤ m ∧
      Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m
        (P*(q:ℝ)^(i+3)*exp (iterationBudgets (i+3) σ η k n).2)
        (iterationBudgets (i+3) σ η k n).1 ((4*classCount i)^n)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨k,by simp,by simpa only [iterationBudgets,pow_zero,show i+3-1=i+2 by omega] using Nonempty.intro e0⟩
    | succ n ih =>
      intro hn
      obtain ⟨m,hm,⟨e⟩⟩:=ih (by omega)
      have hml : c*(q:ℝ)*σ^(1+η) ≤ m:=by
        have hh:=retained_length hr (by positivity : 0 ≤ (q:ℝ)*σ^(1+η)) (by omega : n ≤ T) hklo hm
        simpa only [c,mul_assoc] using hh
      have hL : (0:ℝ) < (4*classCount i)^n:=by positivity
      have hLL : ((4*classCount i)^n:ℝ) ≤ Lstar:=pow_le_pow_right₀ hLone (by omega)
      obtain ⟨m',hm',⟨out⟩⟩:=hstep q hq he Ω N k m p stream F
        (iterationBudgets (i+3) σ η k n).1 (iterationBudgets (i+3) σ η k n).2
        ((4*classCount i)^n) (evenScale σ η) hk hkn hku (hdata n).1 (hdata n).2.1
        hL hLL (hdata n).2.2 hdom hselect hN hcon hocc e hml
      refine ⟨m',?_,?_⟩
      · calc
          (k:ℝ)/r^(n+1) = ((k:ℝ)/r^n)/r:=by rw [pow_succ,div_mul_eq_div_div]
          _ ≤ (m:ℝ)/r:=div_le_div_of_nonneg_right hm hr0.le
          _ ≤ _:=hm'
      · simpa only [iterationBudgets,pow_succ'] using Nonempty.intro out
  obtain ⟨m,hm,⟨e⟩⟩:=hh T le_rfl
  refine ⟨m,?_,⟨e.mono ?_ hΛlast (le_refl _)⟩⟩
  · have hh:=retained_length hr (by positivity : 0 ≤ (q:ℝ)*σ^(1+η)) (le_refl T) hklo hm
    simpa only [c,mul_assoc] using hh
  · exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hΔlast) (by positivity)
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TerminalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales ActualPivot
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.terminalProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.terminalDualProjective
lemma terminal_entropy_upper (i q : ℕ) [Fact q.Prime] (σ P Δ Λ L : ℝ)
    (hσ : 1 ≤ σ) (hP : 1 ≤ P) (hΔ : 0 ≤ Δ) (he : exp σ=(q:ℝ))
    (Ω : Type) [Fintype Ω] (k m : ℕ) (p : Law Ω)
    (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan))
    (e : ContextOutput p (fun x j=>flagPair (F x j)) m (P*(q:ℝ)^(i+3)*exp Δ) Λ L) :
    entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) ≤
      Λ+(m:ℝ)*(((i+3:ℕ):ℝ)*σ+log (3*((i:ℝ)+5))+log 64)+
        (32*((i:ℝ)+5)^3)*(q:ℝ)*σ*(Δ+(|log P|+|log 64|)) := by
  let G:=fun x j=>flagPair (F (e.source x) (e.chosen x j))
  let B:=|log P|+|log 64|
  let J:=jointJ (ZMod q) (i+3)
  have hB : 0 ≤ B:=by dsimp [B];positivity
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hlog : log (q:ℝ)=σ:=by rw [←he,log_exp]
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+1)+3:=by simp
  obtain ⟨hJ0,hBJ,hJgap⟩:=tracked_log_budget i q σ Δ P (zero_le_one.trans hσ) hΔ hP he
  have hprev : ∀ z j,log (e.domains z j).card ≤ J+(Δ+B):=by
    intro z j
    have hh:=e.log_size hJ0 hBJ z j
    change _ ≤ jointJ (ZMod q) (i+3)+(Δ+B)
    linarith
  have hc : ∀ x,e.μ.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=by
    intro x _
    exact scanConsistent_ordered _ (hcons _ (e.supported x)) (e.chosen x)
  have HH:=actual_entropy_upper hdim e.μ e.msg G e.domains (J+(Δ+B)) hc
    (fun x _ j=>(F (e.source x) (e.chosen x j)).incident) (fun x _ j=>e.hit x j) hprev
  have HE:=expected_expensive_bound e.μ G
  have hpoints:=projective_log_card_add_one
    (show Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+3)+1 by simp)
    (by simpa only [Nat.card_zmod,hlog] using hσ)
  rw [Nat.card_zmod,hlog] at hpoints
  have hExp : (32*(Module.finrank (ZMod q) (Fin (i+4)→ZMod q)+1)^2*(Nat.card (ZMod q):ℝ)*
      log (Fintype.card (Points (K:=ZMod q) (V:=Fin (i+4)→ZMod q))+1:ℝ)) ≤
      (32*((i:ℝ)+5)^3)*(q:ℝ)*σ:=by
    simp only [Points] at *
    have hh:=mul_le_mul_of_nonneg_left hpoints
      (by positivity : 0 ≤ 32*((i:ℝ)+5)^2*(q:ℝ))
    simp only [Module.finrank_pi,Fintype.card_fin,Nat.card_zmod]
    push_cast at hh ⊢
    nlinarith only [hh]
  have hj : J=log 64+((i+3:ℕ):ℝ)*σ:=by
    dsimp only [J,jointJ]
    rw [Nat.card_zmod,log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow,hlog]
  have heterm:=mul_le_mul_of_nonneg_right (HE.trans hExp) (add_nonneg hΔ hB)
  have hcost:=e.cost
  change _ ≤ entropy (e.μ.map e.msg)+_+(m:ℝ)*J+_*(J+(Δ+B)-J) at HH
  rw [add_sub_cancel_left,hj] at HH
  simp only [Module.finrank_pi,Fintype.card_fin] at HH
  push_cast at HH
  have hMask : log (((i:ℝ)+4+1)*3)=log (3*((i:ℝ)+5)):=by congr 1;ring
  rw [hMask] at HH
  change entropy (e.μ.map G) ≤ _
  dsimp only [B] at heterm
  push_cast
  nlinarith only [HH,heterm,hcost]
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_TerminalGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.gainProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.gainDualProjective
lemma flag_context_gain (i q : ℕ) [Fact q.Prime] (σ η c Lstar : ℝ)
    (hσ : 1 ≤ σ) (hη : 0 ≤ η) (hc : 0 < c) (hLs : 0 < Lstar)
    (he : exp σ=(q:ℝ))
    (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
    (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (B Λ L : ℝ) (hLL : L ≤ Lstar) (hkn : k ≤ N)
    (hdom : ∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N)
    (hselect : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x))
    (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*σ)
    (e : ContextOutput p (fun x j=>flagPair (F x j)) m B Λ L)
    (hmlo : c*(q:ℝ)*σ^(1+η) ≤ m) :
    (m:ℝ)*(((i+3:ℕ):ℝ)*σ+η*log σ)-(1+|log c|+|log (2*(Lstar*2))|)*m ≤
      entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) := by
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hσ0 : 0 < σ:=by linarith
  have hm : 0 < m:=by
    have hscale : 0 < σ^(1+η):=
      lt_of_lt_of_le zero_lt_one (one_le_rpow hσ (by linarith only [hη]))
    have : (0:ℝ) < m:=(mul_pos (mul_pos hc hq0) hscale).trans_le hmlo
    exact_mod_cast this
  have halphabet:=flag_alphabet_lower i q
  have : Nonempty (Flag (ZMod q) (Fin (i+4)→ZMod q)):=Fintype.card_pos_iff.mp (by
    have : (0:ℝ) < (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ):=(pow_pos hq0 _).trans_le halphabet
    exact_mod_cast this)
  let ee:=e.mono (le_refl _) (le_refl _) hLL
  have hh:=ee.tracked_entropy stream F flagPair flagPair_injective (by intros;rfl)
    (by omega : 1 ≤ i+3) hm hkn (by norm_num : (0:ℝ) < 2) hLs hq0 hσ0 hc
    hdom hselect hN hmlo halphabet
  have hlogq : log (q:ℝ)=σ:=by rw [←he,log_exp]
  rw [hlogq] at hh
  dsimp only [ee,ContextOutput.mono] at hh
  have hh' : (m:ℝ)*(((i+3:ℕ):ℝ)*σ+η*log σ+log c-1)-log (2*(Lstar*2)) ≤
      entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    first | ring | congr!
  have hpos : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hm' : |log (2*(Lstar*2))| ≤ (m:ℝ)*|log (2*(Lstar*2))|:=le_mul_of_one_le_left (abs_nonneg _) hpos
  have hc':=mul_le_mul_of_nonneg_left (neg_abs_le (log c)) (Nat.cast_nonneg m)
  nlinarith only [hh',hm',hc',le_abs_self (log (2*(Lstar*2)))]

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_NoContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales ActualPivot
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.noCtxProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.noCtxDualProjective
theorem eventually_no_small_context (i : ℕ) (η c Lstar P : ℝ)
    (hη : 0 < η) (hc : 0 < c) (hLs : 0 < Lstar) (hP : 1 ≤ P) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
    ∀ (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
      (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q)),
      k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
      (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
      (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
      c*(q:ℝ)*σ^(1+η) ≤ m →
      ¬Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m
        (P*(q:ℝ)^(i+3)*exp (48*σ^(8*beta η))) k Lstar) := by
  let A:=1+|log c|+|log (2*(Lstar*2))|
  let B:=|log P|+|log 64|
  let E:=32*((i:ℝ)+5)^3
  let C:=log (3*((i:ℝ)+5))+log 64+1/c+1
  have hB : 0 ≤ B:=by dsimp [B];positivity
  have hE : 0 ≤ E:=by dsimp [E];positivity
  have hg : 1+8*beta η < 1+η:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power (E*(48+B)) (1+8*beta η) (1+η) c hg hc,
    tendsto_log_atTop.eventually_gt_atTop ((A+C)/η),eventually_ge_atTop (1:ℝ)] with σ hsmall hlog hσ
  intro q _ he Ω _ N k m p stream F hkn hku hdom hsel hN hcons hmlo ⟨e⟩
  have hσ0 : 0 < σ:=by linarith
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hm0 : (0:ℝ) < m:=(by positivity : (0:ℝ) < c*(q:ℝ)*σ^(1+η)).trans_le hmlo
  have hgain:=flag_context_gain i q σ η c Lstar hσ hη.le hc hLs he Ω N k m p stream F
    _ k Lstar (le_refl _) hkn hdom hsel hN e hmlo
  have hu:=terminal_entropy_upper i q σ P (48*σ^(8*beta η)) k Lstar hσ hP (by positivity) he
    Ω k m p F hcons e
  have hp : 1 ≤ σ^(8*beta η):=one_le_rpow hσ (by have:=beta_pos hη;positivity)
  have hdelta : 48*σ^(8*beta η)+B ≤ (48+B)*σ^(8*beta η):=by nlinarith [mul_le_mul_of_nonneg_left hp hB]
  have herr : E*(q:ℝ)*σ*(48*σ^(8*beta η)+B) ≤ m:=by
    calc
      _ ≤ E*(q:ℝ)*σ*((48+B)*σ^(8*beta η)):=mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = (q:ℝ)*(E*(48+B)*σ^(1+8*beta η)):=by rw [rpow_add hσ0,rpow_one];ring
      _ ≤ (q:ℝ)*(c*σ^(1+η)):=mul_le_mul_of_nonneg_left hsmall hq0.le
      _ ≤ _:=by nlinarith only [hmlo]
  have hk : (k:ℝ) ≤ (m:ℝ)/c:=by apply (le_div_iff₀ hc).mpr;nlinarith only [mul_le_mul_of_nonneg_left hku hc.le,hmlo]
  have hgaineq : A+C < η*log σ:=(div_lt_iff₀ hη).mp hlog |>.trans_eq (mul_comm _ _)
  have hstrict:=mul_lt_mul_of_pos_left hgaineq hm0
  change (m:ℝ)*(((i+3:ℕ):ℝ)*σ+η*log σ)-A*m ≤ _ at hgain
  change entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) ≤
    (k:ℝ)+(m:ℝ)*(((i+3:ℕ):ℝ)*σ+log (3*((i:ℝ)+5))+log 64)+
      E*(q:ℝ)*σ*(48*σ^(8*beta η)+B) at hu
  dsimp only [C] at hstrict
  have hk' : (k:ℝ) ≤ (m:ℝ)*(1/c):=by simpa [div_eq_mul_inv] using hk
  nlinarith only [hgain,hu,herr,hk',hstrict]
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_GraphWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.witnessProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.witnessDualProjective
theorem eventually_graph_witness (i : ℕ) (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ N k : ℕ, 0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      ((q:ℝ)*σ^(1+η))/2 ≤ k → (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      ∃ G : SimpleGraph (Fin N),G.CliqueFree (i+4) ∧ G.indepNum < k := by
  let P:=max 4 (stepPrefactor (i+3))
  let T:=⌈8/η⌉₊+1
  let Lstar:ℝ:=(4*classCount i)^T
  let c:ℝ:=(1/2)/(256*classCount i)^T
  have hP4 : 4 ≤ P:=le_max_left _ _
  have hP1 : 1 ≤ P:=by linarith
  have hPs : stepPrefactor (i+3) ≤ P:=le_max_right _ _
  have hK : 0 < classCount i:=classCount_pos i
  have hLs : 0 < Lstar:=by dsimp [Lstar];positivity
  have hc : 0 < c:=by dsimp [c];positivity
  filter_upwards [eventually_iterated_context i η P (InitialExperiment.occupancyConstant i)
    hη hηu hP1 hPs (InitialExperiment.occupancyConstant_pos i).le,
    eventually_no_small_context i η c Lstar P hη hc hLs hP1] with σ hiter hnone
  intro q _ hq he N k hk hkn hku hklo hN
  by_contra! hbad
  have h : ∀ z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q),
      k ≤ (flagGraph (ZMod q) (Fin (i+4)→ZMod q) z).indepNum:=by
    intro z
    exact hbad _ (prime_flagGraph_cliqueFree q (i+3) N z)
  have hlog : log (q:ℝ)=σ:=by rw [←he,log_exp]
  have hNlog : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ):=by simpa only [hlog] using hN
  let Ω:=InitialExperiment.goodEvent i q N
  let p:=InitialExperiment.law i q N hNlog
  let stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q):=Subtype.val
  let F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q):=InitialExperiment.tuple i q N k h
  have hdom : ∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N:=
    InitialExperiment.law_dom i q N hNlog
  have hsel : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x):=by
    intro x _
    exact Or.inr (InitialExperiment.tuple_occurs i q N k h x)
  have hcon : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan):=by
    intro x _
    exact InitialExperiment.tuple_consistent i q N k h x
  have hocc : ∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
    ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
      orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤
        InitialExperiment.occupancyConstant i*σ:=by
    intro x _ W
    simpa only [hlog] using InitialExperiment.tuple_occupancy i q N k h x W
  let e0:=initial_context p F _ (InitialExperiment.alphabet_cap i q hP4 σ he)
  obtain ⟨m,hm,⟨e⟩⟩:=hiter q hq he Ω N k p stream F hk hkn hku hklo hdom hsel hN hcon hocc e0
  exact hnone q he Ω N k m p stream F hkn hku hdom hsel hN hcon hm ⟨e⟩
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_SourceSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.InitialExperiment
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_source_sizes (i : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    ∀ᶠ q : ℕ in atTop,
      3 ≤ q ∧ 1 ≤ log (q:ℝ) ∧
      0 < ⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊ ∧
      ⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊ ≤ ⌊(q:ℝ)^(i+3)*log (q:ℝ)⌋₊ ∧
      (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ) ≤ (q:ℝ)*(log (q:ℝ))^(1+η) ∧
      ((q:ℝ)*(log (q:ℝ))^(1+η))/2 ≤ (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ) ∧
      (⌊(q:ℝ)^(i+3)*log (q:ℝ)⌋₊:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop η (by norm_num : (0:ℝ)<1)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_ge_atTop (3:ℕ)] with q hsmall hl hq
  change 1 ≤ log (q:ℝ) at hl
  have hq1 : (1:ℝ) ≤ q:=by exact_mod_cast (show 1 ≤ q by omega)
  have hq2 : (2:ℝ) ≤ q:=by exact_mod_cast (show 2 ≤ q by omega)
  have hq0 : (0:ℝ) < q:=by linarith
  have hl0 : 0 < log (q:ℝ):=by linarith
  simp only [Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos hl0 _),
    rpow_one,abs_of_pos hq0,one_mul] at hsmall
  have hpow : 1 ≤ (log (q:ℝ))^(1+η):=one_le_rpow hl (by linarith)
  have hQ : 2 ≤ (q:ℝ)*(log (q:ℝ))^(1+η):=by nlinarith only [hpow,hq2]
  have hf : (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ)+1 > (q:ℝ)*(log (q:ℝ))^(1+η):=Nat.lt_floor_add_one _
  have hlower : ((q:ℝ)*(log (q:ℝ))^(1+η))/2 ≤ (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ):=by linarith
  refine ⟨hq,hl,?_,?_,Nat.floor_le (by positivity),hlower,Nat.floor_le (by positivity)⟩
  · exact (Nat.one_le_floor_iff _).mpr (by linarith)
  · apply Nat.floor_mono
    calc
      _ = (q:ℝ)*log (q:ℝ)*(log (q:ℝ))^η:=by rw [rpow_add hl0,rpow_one];ring
      _ ≤ (q:ℝ)*log (q:ℝ)*(q:ℝ):=mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = (q:ℝ)^2*log (q:ℝ):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (by omega : 2 ≤ i+3)) hl0.le
end
end SharpLogRamsey.InitialExperiment

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_PrimeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.LowerTransfer
open Real Filter
open scoped Topology
noncomputable section

theorem actual_prime_construction (i : ℕ) : PrimeConstruction (i+3) := by
  intro η hη hηu
  have hσ:=Marking.eventually_graph_witness i η hη (by linarith : η ≤ 1)
  have ht : Tendsto (fun q : ℕ=>log (q:ℝ)) atTop atTop:=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hσ,InitialExperiment.eventually_source_sizes i η hη.le]
    with q hgraph hsize
  intro hq
  have : Fact q.Prime:=⟨hq⟩
  have hq0 : (0:ℝ) < q:=by exact_mod_cast hq.pos
  exact hgraph q hsize.1 (exp_log hq0) _ _ hsize.2.2.1 hsize.2.2.2.1
    hsize.2.2.2.2.1 hsize.2.2.2.2.2.1 hsize.2.2.2.2.2.2

theorem prime_construction_oai (d : ℕ) (hd : 5 ≤ d) : PrimeConstruction d := by
  have he : d-3+3=d:=by omega
  simpa only [he] using actual_prime_construction (d-3)
end
end SharpLogRamsey.LowerTransfer

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.LowerTransfer.prime_construction_oai := @OAI.SharpLogRamsey.LowerTransfer.prime_construction_oai
