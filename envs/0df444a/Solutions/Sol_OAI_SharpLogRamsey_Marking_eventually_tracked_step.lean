-- Prove2me | solution 1 for OAI.SharpLogRamsey.Marking.eventually_tracked_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:38:07.783771+00:00
-- url     : https://prove2.me/submissions/961b1b21-170a-4d2a-a7c0-824b455fc4c8

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_Marking_eventually_class_step

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

end
end SharpLogRamsey.Selection

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

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingDeficit
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
variable {Ω α Γ M ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι]

omit [Fintype Ω] [Fintype Γ] [Fintype M] in

lemma subset_budget_deficit (p : Law (ι → α)) (S : Finset ι) (J : ι → ℝ)
    (hJ : ∀ i, entropy (p.marginal i) ≤ J i) :
    0 ≤ (∑ i∈S, J i)-entropy (p.restrict S) ∧
    (∑ i∈S, J i)-entropy (p.restrict S) ≤ (∑ i, J i)-entropy p := by
  have hcap (T : Finset ι) : entropy (p.restrict T) ≤ ∑ i∈T, J i := by
    apply (entropy_subadditive_pi _).trans
    simp only [Law.marginal_restrict]
    rw [sum_subtype T (fun _ => Iff.rfl)]
    exact sum_le_sum (fun i _ => hJ i)
  let f := fun x : ι → α => ((fun i:S => x i),(fun i:↥(Sᶜ) => x i))
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    by_cases hi : i∈S
    · exact congr_fun (congrArg Prod.fst hxy) ⟨i,hi⟩
    · exact congr_fun (congrArg Prod.snd hxy) ⟨i,by simpa using hi⟩
  have h1 : (p.map f).fst=p.restrict S := by rw [←Law.map_fst,Law.map_map]; rfl
  have h2 : (p.map f).snd=p.restrict Sᶜ := by rw [←Law.map_snd,Law.map_map]; rfl
  have ht := entropy_subadditive (p.map f)
  rw [entropy_map_eq_of_injective p f hf,h1,h2] at ht
  have hs := sum_add_sum_compl S J
  exact ⟨sub_nonneg.mpr (hcap S),by linarith [hcap Sᶜ]⟩

omit [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι] in
lemma cheap_budget_sum (E S : Finset ι) (J : ℝ) (hS : Disjoint S E) :
    (∑ i∈S, if i∈E then (0:ℝ) else J) = S.card*J := by
  rw [sum_congr rfl (fun i hi => ite_eq_right (disjoint_left.mp hS hi))]
  simp

omit [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] in
lemma cheap_budget_total (E : Finset ι) (J : ℝ) :
    (∑ i, if i∈E then (0:ℝ) else J) = ((Fintype.card ι:ℝ)-E.card)*J := by
  rw [sum_ite,sum_const_zero,zero_add,sum_const,nsmul_eq_mul]
  have hc : (univ.filter (fun i => i∉E)).card=Fintype.card ι-E.card := by
    rw [←sdiff_eq_filter,card_sdiff_of_subset (subset_univ _),card_univ]
  rw [hc,Nat.cast_sub (card_le_univ _)]

lemma marking_subset_pointwise (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (J₀ : ℝ)
    (hc : ∀ x, p.mass x≠0 → ∀ i, i∉E (mask x) →
      F x i∈cheap (markingMessage C mask E F x) i)
    (hcheap : ∀ θ i, i∉E θ.2.2 → Real.log (cheap θ i).card≤J₀)
    (z : (ι → Option α) × (Γ × M))
    (hz : (p.map (markingMessage C mask E F)).mass z≠0)
    (S : Finset ι) (hS : Disjoint S (E z.2.2)) :
    let ν := (p.cond (markingMessage C mask E F) z).map F
    0 ≤ S.card*J₀-entropy (ν.restrict S) ∧
      S.card*J₀-entropy (ν.restrict S) ≤
        ((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀-entropy ν := by
  let θ := markingMessage C mask E F
  let ν := (p.cond θ z).map F
  have hd (i : ι) : entropy (ν.marginal i) ≤ if i∈E z.2.2 then 0 else J₀ := by
    have hm : entropy (ν.marginal i) ≤ Real.log (markingDecodedDomains E cheap z i).card := by
      change entropy (((p.cond θ z).map F).map (fun f => f i)) ≤ _
      rw [Law.map_map]
      apply entropy_mapped_support
      intro x hx
      obtain ⟨hp,he⟩ := p.cond_support θ z hz x hx
      simpa only [Function.comp_apply,←he] using
        markingDecodedDomains_mem C mask E F cheap x (hc x hp) i
    apply hm.trans
    by_cases hi : i∈E z.2.2
    · simp only [markingDecodedDomains,ite_eq_left hi]
      cases z.1 i <;> simp
    · simpa only [markingDecodedDomains,ite_eq_right hi] using hcheap z i hi
  have hh := subset_budget_deficit ν S (fun i => if i∈E z.2.2 then 0 else J₀) hd
  rw [cheap_budget_sum _ _ _ hS,cheap_budget_total] at hh
  exact hh

theorem marking_subset_deficit (p : Law Ω) (C : Ω → Γ) (mask : Ω → M)
    (E : M → Finset ι) (F : Ω → ι → α) (D : Γ → ι → Finset α)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α) (Jprev J₀ : ℝ)
    (hD : ∀ x, p.mass x≠0 → ∀ i, F x i∈D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card≤Jprev)
    (hc : ∀ x, p.mass x≠0 → ∀ i, i∉E (mask x) →
      F x i∈cheap (markingMessage C mask E F x) i)
    (hcheap : ∀ θ i, i∉E θ.2.2 → Real.log (cheap θ i).card≤J₀)
    (S : ((ι → Option α) × (Γ × M)) → Finset ι)
    (hS : ∀ z, Disjoint (S z) (E z.2.2)) :
    let θ := markingMessage C mask E F
    let δ := fun z => (S z).card*J₀-
      entropy (((p.cond θ z).map F).restrict (S z))
    0 ≤ ∑ z, (p.map θ).mass z*δ z ∧
      (∑ z, (p.map θ).mass z*δ z) ≤ entropy (p.map C)+Real.log (Fintype.card M)+
        Fintype.card ι*J₀-entropy (p.map F)+
        (∑ x, p.mass x*((E (mask x)).card:ℝ))*(Jprev-J₀) := by
  dsimp only
  let θ := markingMessage C mask E F
  have hpt z hz := marking_subset_pointwise p C mask E F cheap J₀ hc hcheap z hz (S z) (hS z)
  constructor
  · apply sum_nonneg
    intro z _
    by_cases hz : (p.map θ).mass z=0
    · simp only [θ] at hz
      simp [hz]
    · exact mul_nonneg ((p.map θ).nonneg z) (hpt z hz).1
  · have hp := entropy_context_bound p θ F (fun z => entropy ((p.cond θ z).map F))
        (fun _ _ => le_rfl)
    have hm := marking_message_entropy p C mask E F D Jprev hD hprev
    have he : (∑ z, (p.map θ).mass z * (((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀)) =
        ((Fintype.card ι:ℝ)-∑ x, p.mass x*((E (mask x)).card:ℝ))*J₀ := by
      rw [p.sum_map θ]
      change (∑ x, p.mass x * (((Fintype.card ι:ℝ)-(E (mask x)).card)*J₀)) = _
      simp_rw [←mul_assoc,mul_sub]
      rw [←sum_mul,sum_sub_distrib,←sum_mul,p.total,one_mul]
    have hh : ∑ z, (p.map θ).mass z*((S z).card*J₀-
        entropy (((p.cond θ z).map F).restrict (S z))) ≤
        ∑ z, (p.map θ).mass z*(((Fintype.card ι:ℝ)-(E z.2.2).card)*J₀-
          entropy ((p.cond θ z).map F)) := by
      apply sum_le_sum
      intro z _
      by_cases hz : (p.map θ).mass z=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hpt z hz).2 ((p.map θ).nonneg z)
    simp only [mul_sub,sum_sub_distrib,he] at hh
    change _ ≤ _
    dsimp only [θ] at hp hh
    simp only [mul_sub,sum_sub_distrib]
    linarith

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingTwoScans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma reversedPairs_consistent {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hF : ScanConsistent ((List.ofFn F).map toScan)) :
    ScanConsistent ((List.ofFn (reversedPairs F)).map toScan) := by
  rw [List.map_ofFn] at hF ⊢
  have hh := List.pairwise_ofFn.mp hF
  apply List.pairwise_ofFn.mpr
  intro i j hij
  change Incidence.Incident (F j.rev).2 (bidual (F i.rev).1) →
    Incidence.Incident (F i.rev).2 (bidual (F j.rev).1)
  simp only [incident_bidual]
  exact hh (Fin.rev_lt_rev.mpr hij)

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma reversedPairs_incident {N : ℕ} (F : Fin N → ProjectivePair (K:=K) (V:=V))
    (hF : ∀ i, Incidence.Incident (F i).1 (F i).2) (i : Fin N) :
    Incidence.Incident (reversedPairs F i).1 (reversedPairs F i).2 :=
  (incident_bidual _ _).mpr (hF i.rev)

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma bothExpensive_mem {N : ℕ} (m : TwoMask (K:=K) (V:=V) N) (i : Fin N) :
    i∈bothExpensive m ↔ i∈expensiveMask m.1 ∨ i.rev∈expensiveMask m.2 := by
  simp only [bothExpensive,mem_union,mem_image]
  constructor
  · rintro (h|⟨j,hj,hji⟩)
    · exact Or.inl h
    · right
      simpa only [←hji,Fin.rev_rev] using hj
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨i.rev,h,Fin.rev_rev i⟩

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstMessage_actual {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (x : Ω) (q : ℝ) :
    firstMessage (Selection.markingMessage C (fun x => twoMask q (F x)) bothExpensive F x) =
      (Selection.maskedValues (expensiveMask (tupleMask q (F x))) (F x),
        (C x,tupleMask q (F x))) := by
  apply Prod.ext
  · funext i
    change (if i∈expensiveMask (tupleMask q (F x)) then
      Selection.maskedValues (bothExpensive (twoMask q (F x))) (F x) i else none)=_
    by_cases hi : i∈expensiveMask (tupleMask q (F x))
    · have hb : i∈bothExpensive (twoMask q (F x)) := (bothExpensive_mem _ _).mpr (Or.inl hi)
      simp only [hi,ite_true,Selection.maskedValues,hb]
    · simp only [hi,ite_false,Selection.maskedValues]
  · rfl

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondMessage_actual {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (x : Ω) (q : ℝ) :
    secondMessage (Selection.markingMessage C (fun x => twoMask q (F x)) bothExpensive F x) =
      (Selection.maskedValues (expensiveMask (tupleMask q (reversedPairs (F x))))
        (reversedPairs (F x)),(C x,tupleMask q (reversedPairs (F x)))) := by
  apply Prod.ext
  · funext i
    change (if i∈expensiveMask (tupleMask q (reversedPairs (F x))) then
      (Selection.maskedValues (bothExpensive (twoMask q (F x))) (F x) i.rev).map pairDuality
      else none)=_
    by_cases hi : i∈expensiveMask (tupleMask q (reversedPairs (F x)))
    · have hb : i.rev∈bothExpensive (twoMask q (F x)) := by
        apply (bothExpensive_mem _ _).mpr
        right
        simpa only [Fin.rev_rev,twoMask] using hi
      simp only [hi,ite_true,Selection.maskedValues,hb,Option.map_some,reversedPairs]
    · simp only [hi,ite_false,Selection.maskedValues]
  · rfl

lemma cheapBoth_mem {Ω Γ : Type*} {N : ℕ} (C : Ω → Γ)
    (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V)) (x : Ω)
    (hcons : ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ i, Incidence.Incident (F x i).1 (F x i).2) (i : Fin N)
    (hi : i∉bothExpensive (twoMask (Nat.card K) (F x))) :
    F x i∈cheapBoth (Selection.markingMessage C (fun x => twoMask (Nat.card K) (F x))
      bothExpensive F x) i := by
  have hn := not_or.mp ((bothExpensive_mem _ _).not.mp hi)
  apply mem_inter.mpr
  constructor
  · change F x i∈cheapTuple (firstMessage _) i
    rw [firstMessage_actual]
    exact cheapTuple_mem (C x) (F x) hcons hinc i hn.1
  · change F x i∈(cheapTuple (secondMessage _) i.rev).map pairDuality.symm.toEmbedding
    rw [secondMessage_actual]
    apply mem_map.mpr
    refine ⟨reversedPairs (F x) i.rev,?_,?_⟩
    · exact cheapTuple_mem (C x) (reversedPairs (F x)) (reversedPairs_consistent _ hcons)
        (reversedPairs_incident _ hinc) i.rev hn.2
    · simp only [Equiv.coe_toEmbedding,reversedPairs,Fin.rev_rev,Equiv.symm_apply_apply]

variable [Finite K]
lemma cheapBoth_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    ((cheapBoth z i).card:ℝ) ≤ 64*(Nat.card K:ℝ)^(n+2) := by
  have h : ((cheapBoth z i).card:ℝ) ≤ (cheapTuple (firstMessage z) i).card := by
    exact_mod_cast (card_le_card (inter_subset_left : cheapBoth z i⊆_))
  exact h.trans (cheapTuple_card hdim (firstMessage z) i)

lemma cheapBoth_log_card {Γ : Type*} {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    Real.log (cheapBoth z i).card≤Real.log (64*(Nat.card K:ℝ)^(n+2)) := by
  by_cases hz : (cheapBoth z i).card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
    exact Real.log_nonneg (by nlinarith [(one_le_pow₀ hq : (1:ℝ)≤(Nat.card K:ℝ)^(n+2))])
  · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hz)) (cheapBoth_card hdim z i)

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K] in

lemma bothExpensive_card {N : ℕ} (q : ℝ) (F : Fin N → ProjectivePair (K:=K) (V:=V)) :
    (bothExpensive (twoMask q F)).card ≤
      (expensiveMask (tupleMask q F)).card+
      (expensiveMask (tupleMask q (reversedPairs F))).card := by
  exact card_union_le _ _ |>.trans (Nat.add_le_add_left (card_image_le) _)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_MarkingTwoEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem twoScan_subset_deficit {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω → Γ) (F : Ω → Fin N → ProjectivePair (K:=K) (V:=V))
    (D : Γ → Fin N → Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x, p.mass x≠0 → ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x, p.mass x≠0 → ∀ i, Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x, p.mass x≠0 → ∀ i, F x i∈D (C x) i)
    (hprev : ∀ c i, Real.log (D c i).card≤Jprev)
    (S : TwoMessage (K:=K) (V:=V) Γ N → Finset (Fin N))
    (hS : ∀ z, Disjoint (S z) (bothExpensive z.2.2)) :
    0 ≤ Selection.selectedDeficit p (sourceMessage C F) F S (jointJ K (n+2)) ∧
      Selection.selectedDeficit p (sourceMessage C F) F S (jointJ K (n+2)) ≤
        excessCost p C F Jprev (jointJ K (n+2)) := by
  have hh := Selection.marking_subset_deficit p C (fun x => twoMask (Nat.card K) (F x))
    bothExpensive F D cheapBoth Jprev (jointJ K (n+2)) hD hprev
    (fun x hx i hi => cheapBoth_mem C F x (hcons x hx) (hinc x hx) i hi)
    (fun z i _ => cheapBoth_log_card hdim z i) S hS
  change 0≤_ ∧ _≤_ at hh
  convert hh using 1 <;> simp only [Selection.selectedDeficit,sourceMessage,excessCost,Fintype.card_fin]
  all_goals congr!

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ α ι : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype ι]

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_map_mass (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (z : Γ) :
    ((p.onContextEvent θ E hE).map θ).mass z =
      if z∈E then (p.map θ).mass z/(p.map θ).event E else 0 := by
  change (∑ x with θ x=z, if θ x∈E then p.mass x/(p.map θ).event E else 0)=_
  by_cases hz : z∈E
  · rw [ite_eq_left hz]
    change _=(∑ x with θ x=z,p.mass x)/(p.map θ).event E
    rw [sum_div]
    apply sum_congr rfl
    intro x hx
    rw [ite_eq_left (by simpa only [(mem_filter.mp hx).2] using hz)]
  · rw [ite_eq_right hz]
    apply sum_eq_zero
    intro x hx
    exact ite_eq_right (by simpa only [(mem_filter.mp hx).2] using hz)

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_support (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (x : Ω) (hx : (p.onContextEvent θ E hE).mass x≠0) :
    p.mass x≠0 ∧ θ x∈E := by
  change (if θ x∈E then p.mass x/(p.map θ).event E else 0)≠0 at hx
  split_ifs at hx with he
  · exact ⟨(div_ne_zero_iff.mp hx).1,he⟩
  · exact False.elim (hx rfl)

omit [Fintype α] [Fintype ι] in

lemma Law.onContextEvent_cond (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (z : Γ)
    (hz : ((p.onContextEvent θ E hE).map θ).mass z≠0) :
    (p.onContextEvent θ E hE).cond θ z=p.cond θ z := by
  have hm := p.onContextEvent_map_mass θ E hE z
  have hzE : z∈E := by by_contra hn; rw [hm,ite_eq_right hn] at hz; exact hz rfl
  have hp : (p.map θ).mass z≠0 := by
    rw [hm,ite_eq_left hzE] at hz
    exact (div_ne_zero_iff.mp hz).1
  ext x
  rw [Law.cond_mass _ _ _ hz,Law.cond_mass _ _ _ hp,hm,ite_eq_left hzE]
  by_cases hx : θ x=z
  · simp only [Law.onContextEvent,hx,ite_eq_left hzE,ite_true]
    field_simp
  · simp only [ite_eq_right hx,zero_div]

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_domination (p q : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (C : ℝ)
    (hC : ∀ x,p.mass x≤C*q.mass x) :
    ∀ x,(p.onContextEvent θ E hE).mass x≤(C/(p.map θ).event E)*q.mass x := by
  intro x
  have hh := div_le_div_of_nonneg_right (hC x) (le_of_lt hE)
  change (if θ x∈E then p.mass x/(p.map θ).event E else 0)≤_
  have hh' : p.mass x/(p.map θ).event E≤(C/(p.map θ).event E)*q.mass x := by
    calc
      _ ≤ (C*q.mass x)/(p.map θ).event E := hh
      _ = _ := by ring
  split_ifs
  · exact hh'
  · exact (div_nonneg (p.nonneg x) (le_of_lt hE)).trans hh'

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_expectation (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (g : Γ→ℝ)
    (hg : ∀ z,(p.map θ).mass z≠0→0≤g z) :
    (∑ z, ((p.onContextEvent θ E hE).map θ).mass z*g z) ≤
      (∑ z,(p.map θ).mass z*g z)/(p.map θ).event E := by
  rw [sum_div]
  apply sum_le_sum
  intro z _
  rw [p.onContextEvent_map_mass θ E hE]
  by_cases hz : z∈E
  · rw [ite_eq_left hz]
    apply le_of_eq
    ring
  · rw [ite_eq_right hz,zero_mul]
    apply div_nonneg _ (le_of_lt hE)
    by_cases hp : (p.map θ).mass z=0
    · simp [hp]
    · exact mul_nonneg ((p.map θ).nonneg z) (hg z hp)

theorem selectedDeficit_onContextEvent (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (F : Ω→ι→α) (S : Γ→Finset ι) (J : ℝ)
    (hδ : ∀ z,(p.map θ).mass z≠0→
      0≤(S z).card*J-entropy (((p.cond θ z).map F).restrict (S z))) :
    selectedDeficit (p.onContextEvent θ E hE) θ F S J≤
      selectedDeficit p θ F S J/(p.map θ).event E := by
  have he : selectedDeficit (p.onContextEvent θ E hE) θ F S J=
      ∑ z,((p.onContextEvent θ E hE).map θ).mass z*
        ((S z).card*J-entropy (((p.cond θ z).map F).restrict (S z))) := by
    apply sum_congr rfl
    intro z _
    by_cases hz : ((p.onContextEvent θ E hE).map θ).mass z=0
    · simp only [hz,zero_mul]
    · rw [p.onContextEvent_cond θ E hE z hz]
  rw [he]
  exact p.onContextEvent_expectation θ E hE _ hδ

theorem selectedDeficit_onContextEvent_le (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (F : Ω→ι→α) (S : Γ→Finset ι) (J B : ℝ)
    (hδ : ∀ z,(p.map θ).mass z≠0→
      0≤(S z).card*J-entropy (((p.cond θ z).map F).restrict (S z)))
    (hB : selectedDeficit p θ F S J≤B) :
    selectedDeficit (p.onContextEvent θ E hE) θ F S J≤B/(p.map θ).event E :=
  (selectedDeficit_onContextEvent p θ E hE F S J hδ).trans
    (div_le_div_of_nonneg_right hB hE.le)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ ι κ : Type*} [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ]

theorem exists_fixed_class (p : Law Ω) (θ : Ω→Γ) (U : Γ→Finset ι)
    (colour : Γ→ι→κ) (n : ℕ)
    (hcard : ∀ x,p.mass x≠0→Fintype.card κ*n≤(U (θ x)).card) :
    ∃ c : κ,1/(Fintype.card κ:ℝ)≤
      (p.map θ).event (univ.filter (fun z=>n≤(classSlots U colour z c).card)) := by
  have hex z (hz : (p.map θ).mass z≠0) :
      ∃ c : κ,n≤(classSlots U colour z c).card := by
    obtain ⟨x,hx,rfl⟩ := p.map_support θ z hz
    obtain ⟨c,_,hc⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s:=U (θ x)) (t:=univ) (f:=colour (θ x)) (n:=n)
      (fun _ _=>mem_univ _) univ_nonempty (by simpa using hcard x hx)
    exact ⟨c,hc⟩
  let win : Γ→κ := fun z=>if hz : (p.map θ).mass z≠0 then Classical.choose (hex z hz)
    else Classical.choice inferInstance
  have hw z (hz : (p.map θ).mass z≠0) : n≤(classSlots U colour z (win z)).card := by
    simp only [win,dite_eq_left hz]
    exact Classical.choose_spec (hex z hz)
  have hp : (0:ℝ)<Fintype.card κ := by exact_mod_cast Fintype.card_pos
  obtain ⟨c,hc⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum
    (f:=win) (w:=(p.map θ).mass) (b:=1/(Fintype.card κ:ℝ)) (by
      rw [nsmul_eq_mul,(p.map θ).total]
      exact le_of_eq (mul_one_div_cancel (ne_of_gt hp)))
  refine ⟨c,hc.trans ?_⟩
  simp only [Law.event,sum_filter]
  apply sum_le_sum
  intro z _
  by_cases hz : (p.map θ).mass z=0
  · simp [hz]
  by_cases hc' : win z=c
  · rw [ite_eq_left hc',ite_eq_left (by simpa only [hc'] using hw z hz)]
  · rw [ite_eq_right hc']
    split_ifs
    · exact (p.map θ).nonneg z
    · exact le_refl 0

omit [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ] in
lemma fixedSubset_spec (A : Finset ι) (n : ℕ) (hn : n≤A.card) :
    fixedSubset A n⊆A ∧ (fixedSubset A n).card=n := by
  simp only [fixedSubset,dite_eq_left hn]
  exact Classical.choose_spec (exists_subset_card_eq hn)

theorem common_class_extraction (p : Law Ω) (θ : Ω→Γ) (U : Γ→Finset ι)
    (colour : Γ→ι→κ) (n : ℕ)
    (hcard : ∀ x,p.mass x≠0→Fintype.card κ*n≤(U (θ x)).card) :
    ∃ (c : κ) (E : Finset Γ) (S : Γ→Finset ι),
      1/(Fintype.card κ:ℝ)≤(p.map θ).event E ∧
      (∀ z∈E,(S z).card=n ∧ S z⊆U z ∧ ∀ i∈S z,colour z i=c) := by
  obtain ⟨c,hc⟩ := exists_fixed_class p θ U colour n hcard
  refine ⟨c,univ.filter (fun z=>n≤(classSlots U colour z c).card),
    (fun z=>fixedSubset (classSlots U colour z c) n),hc,?_⟩
  intro z hz
  obtain ⟨hs,hn⟩ := fixedSubset_spec (classSlots U colour z c) n (mem_filter.mp hz).2
  refine ⟨hn,hs.trans (filter_subset _ _),?_⟩
  intro i hi
  exact (mem_filter.mp (hs hi)).2

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingClassSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma two_expensive_bound {N : ℕ} (F : Fin N→ProjectivePair (K:=K) (V:=V)) :
    ((bothExpensive (twoMask (Nat.card K) F)).card:ℝ)≤
      expensiveBudget K V+expensiveBudget K (Module.Dual K V) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have h₁ := scan_expensive_bound (Nat.card K:ℝ) hq (fun _=>⊥) ((List.ofFn F).map toScan)
  have h₂ := scan_expensive_bound (Nat.card K:ℝ) hq (fun _=>⊥)
    ((List.ofFn (reversedPairs F)).map toScan)
  have h := bothExpensive_card (Nat.card K) F
  have h' : ((bothExpensive (twoMask (Nat.card K) F)).card:ℝ)≤
      (expensiveMask (tupleMask (Nat.card K) F)).card+
      (expensiveMask (tupleMask (Nat.card K) (reversedPairs F))).card := by exact_mod_cast h
  rw [expensiveMask_card,expensiveMask_card] at h'
  exact h'.trans (add_le_add h₁ h₂)

variable {Ω Γ κ : Type*} [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ]

omit [Fintype κ] [Nonempty κ] in
lemma twoScan_subset_pointwise {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (z : TwoMessage (K:=K) (V:=V) Γ N)
    (hz : (p.map (sourceMessage C F)).mass z≠0)
    (S : Finset (Fin N)) (hS : Disjoint S (bothExpensive z.2.2)) :
    0≤S.card*jointJ K (n+2)-Selection.entropy
      (((p.cond (sourceMessage C F) z).map F).restrict S) := by
  let θ := sourceMessage C F
  let ν := (p.cond θ z).map F
  have hcoord (i : S) : Selection.entropy ((ν.restrict S).marginal i) ≤ jointJ K (n+2) := by
    rw [Selection.Law.marginal_restrict]
    have hs : Selection.entropy (ν.marginal (i:Fin N)) ≤
        Real.log (cheapBoth z i).card := by
      change Selection.entropy (((p.cond θ z).map F).map (fun f=>f i)) ≤ _
      rw [Selection.Law.map_map]
      apply Selection.entropy_mapped_support
      intro x hx
      obtain ⟨hx,he⟩ := p.cond_support θ z hz x hx
      have hi : (i:Fin N)∉bothExpensive (twoMask (Nat.card K) (F x)) := by
        have he' : twoMask (Nat.card K) (F x)=z.2.2 := congrArg (fun z=>z.2.2) he
        rw [he']
        exact disjoint_left.mp hS i.property
      have hh := cheapBoth_mem C F x (hcons x hx) (hinc x hx) i hi
      simpa only [Function.comp_apply,←he,θ,sourceMessage] using hh
    exact hs.trans (cheapBoth_log_card hdim z i)
  have hh := (Selection.entropy_subadditive_pi (ν.restrict S)).trans
    (sum_le_sum (fun i _=>hcoord i))
  have he : (∑ _ : S,jointJ K (n+2))=S.card*jointJ K (n+2) := by simp
  rw [he] at hh
  exact sub_nonneg.mpr hh

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem actual_common_class_slots {N : ℕ}
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (colour : TwoMessage (K:=K) (V:=V) Γ N→Fin N→κ) (m : ℕ)
    (hm : (Fintype.card κ*m:ℕ)+expensiveBudget K V+
      expensiveBudget K (Module.Dual K V)≤(N:ℝ)) :
    ∃ (c : κ) (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
      (_hE : 0<(p.map (sourceMessage C F)).event E)
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)),
      1/(Fintype.card κ:ℝ)≤(p.map (sourceMessage C F)).event E ∧
      (∀ z,Disjoint (S z) (bothExpensive z.2.2)) ∧
      (∀ z∈E,(S z).card=m ∧ ∀ i∈S z,colour z i=c) := by

  let θ:=sourceMessage C F
  let U:=fun z : TwoMessage (K:=K) (V:=V) Γ N=>(bothExpensive z.2.2)ᶜ
  have hcount x (_hx : p.mass x≠0) : Fintype.card κ*m≤(U (θ x)).card := by
    have hb := two_expensive_bound (F x)
    have hc : ((U (θ x)).card:ℝ)=(N:ℝ)-(bothExpensive (twoMask (Nat.card K) (F x))).card := by
      simp only [U,θ,sourceMessage,Selection.markingMessage,card_compl,
        Fintype.card_fin]
      rw [Nat.cast_sub (by simpa only [Fintype.card_fin] using
        (card_le_univ (bothExpensive (twoMask (Nat.card K) (F x)))))]
    have hh : (Fintype.card κ*m:ℕ)≤((U (θ x)).card:ℝ) := by rw [hc]; linarith
    exact_mod_cast hh
  obtain ⟨c,E,S,hprob,hslots⟩ := Selection.common_class_extraction p θ U colour m hcount
  have hp : 0<(p.map θ).event E := lt_of_lt_of_le (one_div_pos.mpr (by
    exact_mod_cast (Fintype.card_pos (α:=κ)))) hprob
  let S' := fun z=>if z∈E then S z else ∅
  have hS z : Disjoint (S' z) (bothExpensive z.2.2) := by
    by_cases hz : z∈E
    · simp only [S',ite_eq_left hz]
      apply disjoint_left.mpr
      intro i hi hie
      exact (mem_compl.mp ((hslots z hz).2.1 hi)) hie
    · simp [S',hz]
  refine ⟨c,E,hp,S',hprob,hS,?_⟩
  intro z hz
  simpa only [S',ite_eq_left hz] using ⟨(hslots z hz).1,(hslots z hz).2.2⟩

omit [Fintype κ] [Nonempty κ] in

theorem twoScan_conditioned_deficit {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (D : Γ→Fin N→Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Jprev)
    (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
    (hp : 0<(p.map (sourceMessage C F)).event E)
    (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N))
    (hS : ∀ z,Disjoint (S z) (bothExpensive z.2.2)) :
    conditionedDeficit p C F E hp S (jointJ K (n+2)) ≤
      excessCost p C F Jprev (jointJ K (n+2))/(p.map (sourceMessage C F)).event E := by
  unfold conditionedDeficit
  apply Selection.selectedDeficit_onContextEvent_le
  · intro z hz
    convert twoScan_subset_pointwise hdim p C F hcons hinc z hz (S z) (hS z) using 1; congr!
  · exact (twoScan_subset_deficit hdim p C F D Jprev hcons hinc hD hprev S hS).2

theorem actual_common_class {N n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (D : Γ→Fin N→Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Jprev)
    (colour : TwoMessage (K:=K) (V:=V) Γ N→Fin N→κ) (m : ℕ)
    (hm : (Fintype.card κ*m:ℕ)+expensiveBudget K V+
      expensiveBudget K (Module.Dual K V)≤(N:ℝ)) :
    ∃ (c : κ) (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
      (hE : 0<(p.map (sourceMessage C F)).event E)
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)),
      1/(Fintype.card κ:ℝ)≤(p.map (sourceMessage C F)).event E ∧
      (∀ z,Disjoint (S z) (bothExpensive z.2.2)) ∧
      (∀ z∈E,(S z).card=m ∧ ∀ i∈S z,colour z i=c) ∧
      conditionedDeficit p C F E hE S (jointJ K (n+2)) ≤
        excessCost p C F Jprev (jointJ K (n+2))/(p.map (sourceMessage C F)).event E := by
  obtain ⟨c,E,hp,S,hprob,hS,hslots⟩ := actual_common_class_slots p C F colour m hm
  exact ⟨c,E,hp,S,hprob,hS,hslots,
    twoScan_conditioned_deficit hdim p C F D Jprev hcons hinc hD hprev E hp S hS⟩

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingFiniteClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset ReciprocalBands
open scoped Classical
noncomputable section

lemma slotClass_card (d : ℕ) : Fintype.card (SlotClass d)=2*(d+1)+(d+1)^2 := by
  simp only [SlotClass,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,pow_two]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

lemma messageClass_valid {n N : ℕ} {Γ : Type*} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap) (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N)
    (h : (cheapBoth z i).Nonempty) :
    ValidSlotClass (n+2) gap (cheapBoth z i) (messageClass hdim hgap z i) := by
  rw [messageClass,dite_eq_left h]
  exact (cheapBoth_valid_slot_class hdim hgap z i h).choose_spec

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_MarkingGeometricClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]
  {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem actual_geometric_class {N n : ℕ} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap)
    (p : Selection.Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (D : Γ→Fin N→Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Jprev)
    (m : ℕ)
    (hm : ((2*(n+3)+(n+3)^2)*m:ℕ)+expensiveBudget K V+
      expensiveBudget K (Module.Dual K V)≤(N:ℝ)) :
    ∃ (c : SlotClass (n+2)) (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
      (hE : 0<(p.map (sourceMessage C F)).event E)
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)),
      1/((2*(n+3)+(n+3)^2:ℕ):ℝ)≤(p.map (sourceMessage C F)).event E ∧
      (∀ z,Disjoint (S z) (bothExpensive z.2.2)) ∧
      (∀ z∈E,(S z).card=m) ∧
      (∀ x,p.mass x≠0→sourceMessage C F x∈E→∀ i∈S (sourceMessage C F x),
        F x i∈cheapBoth (sourceMessage C F x) i ∧
        ValidSlotClass (n+2) gap (cheapBoth (sourceMessage C F x) i) c) ∧
      conditionedDeficit p C F E hE S (jointJ K (n+2)) ≤
        excessCost p C F Jprev (jointJ K (n+2))/(p.map (sourceMessage C F)).event E := by
  have hcard : Fintype.card (SlotClass (n+2))=2*(n+3)+(n+3)^2 := by
    simpa only [Nat.add_assoc] using slotClass_card (n+2)
  obtain ⟨c,E,hE,S,hprob,hS,hslots,hdef⟩ :=
    actual_common_class hdim p C F D Jprev hcons hinc hD hprev
      (messageClass hdim hgap) m (by simpa only [hcard] using hm)
  refine ⟨c,E,hE,S,?_,hS,(fun z hz=>(hslots z hz).1),?_,hdef⟩
  · simpa only [hcard] using hprob
  · intro x hx he i hi
    have hm := cheapBoth_mem C F x (hcons x hx) (hinc x hx) i
      (disjoint_left.mp (hS (sourceMessage C F x)) hi)
    refine ⟨hm,?_⟩
    have hc := messageClass_valid hdim hgap (sourceMessage C F x) i ⟨F x i,hm⟩
    rwa [(hslots _ he).2 i hi] at hc

end
end SharpLogRamsey.Marking

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
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Γ α β : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β]

omit [Fintype Γ] in
lemma Law.map_congr_support (p : Law Ω) (f g : Ω→α)
    (h : ∀ x,p.mass x≠0→f x=g x) : p.map f=p.map g := by
  ext y
  change (∑ x with f x=y,p.mass x)=(∑ x with g x=y,p.mass x)
  simp only [sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : p.mass x=0
  · simp only [hx,ite_self]
  · rw [h x hx]

omit [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β] in
lemma chosenOrder_mem {N m : ℕ} (S : Γ→Finset (Fin N)) (hm : m≤N) (z : Γ)
    (hs : (S z).card=m) (i : Fin m) : chosenOrder S hm z i∈S z := by
  rw [chosenOrder,dite_eq_left hs]
  exact orderEmbOfFin_mem _ _ _

omit [Fintype β] in

theorem ordered_cond_entropy {N m : ℕ} (p : Law Ω) (θ : Ω→Γ) (F : Ω→Fin N→α)
    (S : Γ→Finset (Fin N)) (hm : m≤N) (z : Γ)
    (hz : (p.map θ).mass z≠0) (hs : (S z).card=m) :
    entropy ((p.cond θ z).map (orderedTuple S hm θ F))=
      entropy (((p.cond θ z).map F).restrict (S z)) := by
  let e := (S z).orderIsoOfFin hs
  let relabel : (S z→α)→(Fin m→α) := fun f i=>f (e i)
  have hi : Function.Injective relabel := by
    intro f g h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun h j
  have he : (p.cond θ z).map (orderedTuple S hm θ F)=
      (((p.cond θ z).map F).restrict (S z)).map relabel := by
    rw [Law.restrict,Law.map_map,Law.map_map]
    apply Law.map_congr_support
    intro x hx
    have hxθ := (p.cond_support θ z hz x hx).2
    funext i
    simp only [orderedTuple,hxθ,chosenOrder,dite_eq_left hs,Function.comp_apply,relabel,e]
    rfl
  rw [he]
  exact entropy_map_eq_of_injective _ relabel hi

omit [Fintype β] in

theorem ordered_deficit {N m : ℕ} (p : Law Ω) (θ : Ω→Γ) (F : Ω→Fin N→α)
    (S : Γ→Finset (Fin N)) (hm : m≤N)
    (hs : ∀ z,(p.map θ).mass z≠0→(S z).card=m) (J : ℝ) :
    (∑ z,(p.map θ).mass z*((m:ℝ)*J-
      entropy ((p.cond θ z).map (orderedTuple S hm θ F))))=
      selectedDeficit p θ F S J := by
  unfold selectedDeficit
  apply sum_congr rfl
  intro z _
  by_cases hz : (p.map θ).mass z=0
  · simp only [hz,zero_mul]
  · rw [ordered_cond_entropy p θ F S hm z hz (hs z hz),hs z hz]
    congr!

end
end SharpLogRamsey.Selection

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
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ActualClassLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Selection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]
  {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem actual_ordered_class {N n : ℕ} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap)
    (p : Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (D : Γ→Fin N→Finset (ProjectivePair (K:=K) (V:=V))) (Jprev : ℝ)
    (hcons : ∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan))
    (hinc : ∀ x,p.mass x≠0→∀ i,Incidence.Incident (F x i).1 (F x i).2)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (C x) i)
    (hprev : ∀ c i,Real.log (D c i).card≤Jprev)
    (m : ℕ)
    (hm : ((2*(n+3)+(n+3)^2)*m:ℕ)+expensiveBudget K V+
      expensiveBudget K (Module.Dual K V)≤(N:ℝ)) :
    ∃ (c : SlotClass (n+2)) (E : Finset (TwoMessage (K:=K) (V:=V) Γ N))
      (hE : 0<(p.map (sourceMessage C F)).event E)
      (S : TwoMessage (K:=K) (V:=V) Γ N→Finset (Fin N)) (hmn : m≤N),
      let θ:=sourceMessage C F
      let p':=p.onContextEvent θ E hE
      let e:=chosenOrder S hmn
      let G:=orderedTuple S hmn θ F
      1/((2*(n+3)+(n+3)^2:ℕ):ℝ)≤(p.map θ).event E ∧
      (∀ z,(p'.map θ).mass z≠0→(S z).card=m) ∧
      (∀ x,p'.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan)) ∧
      (∀ x,p'.mass x≠0→∀ i,Incidence.Incident (G x i).1 (G x i).2) ∧
      (∀ x,p'.mass x≠0→∀ i,
        G x i∈cheapBoth (θ x) (e (θ x) i) ∧
        ValidSlotClass (n+2) gap (cheapBoth (θ x) (e (θ x) i)) c) ∧
      (∑ z,(p'.map θ).mass z*((m:ℝ)*jointJ K (n+2)-entropy ((p'.cond θ z).map G)))≤
        excessCost p C F Jprev (jointJ K (n+2))/(p.map θ).event E := by
  obtain ⟨c,E,hE,S,hprob,hdis,hcard,hgeom,hdef⟩ :=
    actual_geometric_class hdim hgap p C F D Jprev hcons hinc hD hprev m hm
  have hEn : E.Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he] at hE
    simp only [Law.event,sum_empty,lt_self_iff_false] at hE
  obtain ⟨z,hz⟩ := hEn
  have hmn : m≤N := by
    have hh:=card_le_univ (S z)
    simpa only [Fintype.card_fin,hcard z hz] using hh
  let θ:=sourceMessage C F
  let p':=p.onContextEvent θ E hE
  have hcard' z (hz : (p'.map θ).mass z≠0) : (S z).card=m := by
    apply hcard z
    by_contra hn
    have he:=p.onContextEvent_map_mass θ E hE z
    rw [ite_eq_right hn] at he
    exact hz he
  refine ⟨c,E,hE,S,hmn,hprob,hcard',?_,?_,?_,?_⟩
  · intro x hx
    exact scanConsistent_ordered (F x)
      (hcons x ((p.onContextEvent_support θ E hE x hx).1)) (chosenOrder S hmn (θ x))
  · intro x hx i
    exact hinc x ((p.onContextEvent_support θ E hE x hx).1) _
  · intro x hx i
    obtain ⟨hx,he⟩:=p.onContextEvent_support θ E hE x hx
    exact hgeom x hx he _ (chosenOrder_mem S hmn (θ x) (hcard _ he) i)
  · calc
      _ = selectedDeficit p' θ F S (jointJ K (n+2)) :=
        ordered_deficit p' θ F S hmn hcard' _
      _ ≤ _ := hdef

end
end SharpLogRamsey.Marking

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
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RestrictionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

lemma count_injective_restriction {I J : Type} [Fintype I] [Fintype J]
    (e : I↪J) (P : J→Prop) :
    (univ.filter (fun i=>P (e i))).card≤(univ.filter P).card := by
  calc
    _ = ((univ.filter (fun i=>P (e i))).image e).card := by
      rw [card_image_of_injective _ e.injective]
    _ ≤ _ := card_le_card (by
      intro j hj
      obtain ⟨i,hi,rfl⟩:=mem_image.mp hj
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩)

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
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ExcessCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Selection ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [FiniteDimensional K V] [Finite K]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma twoMask_log_card {N d : ℕ} (hdim : Module.finrank K V=d+3) :
    log (Fintype.card (TwoMask (K:=K) (V:=V) N):ℝ)=
      2*(N:ℝ)*log (3*((d:ℝ)+4)) := by
  unfold TwoMask
  rw [Fintype.card_prod]
  simp only [Fintype.card_fun,Fintype.card_fin,rankMask_card,Subspace.dual_finrank_eq,
    hdim,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [log_mul (by positivity) (by positivity),log_pow]
  push_cast
  ring_nf

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma twoExpensive_linear {d : ℕ} (hdim : Module.finrank K V=d+3)
    {σ : ℝ} (hlog : log (Nat.card K:ℝ)=σ) (hσ : 1≤σ) :
    expensiveBudget K V+expensiveBudget K (Module.Dual K V)≤
      (64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ := by
  have hdim' : Module.finrank K V=(d+2)+1:=hdim
  have hdual : Module.finrank K (Module.Dual K V)=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdim]
  have ha:=projective_log_card_add_one hdim' (by rwa [hlog])
  have hb:=projective_log_card_add_one hdual (by rwa [hlog])
  rw [hlog] at ha hb
  unfold expensiveBudget
  simp only [Subspace.dual_finrank_eq,hdim]
  simp only [Points] at *
  push_cast at ha hb ⊢
  have hfactor : 0≤32*((d:ℝ)+3+1)^2*(Nat.card K:ℝ):=by positivity
  have ha':=mul_le_mul_of_nonneg_left ha hfactor
  have hb':=mul_le_mul_of_nonneg_left hb hfactor
  nlinarith only [ha',hb']

variable {Ω Γ : Type} [Fintype Ω] [Fintype Γ]

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem excessCost_linear {N d : ℕ} (hdim : Module.finrank K V=d+3)
    (p : Law Ω) (C : Ω→Γ) (F : Ω→Fin N→ProjectivePair (K:=K) (V:=V))
    (σ Λ Δ A B Jprev : ℝ) (hlog : log (Nat.card K:ℝ)=σ) (hσ : 1≤σ)
    (hΔ : 0≤Δ) (hB : 0≤B) (hC : entropy (p.map C)≤Λ)
    (hF : (N:ℝ)*((d+2:ℕ):ℝ)*σ-A*N≤entropy (p.map F))
    (hJ : Jprev-jointJ K (d+2)≤Δ+B) :
    excessCost p C F Jprev (jointJ K (d+2))≤
      Λ+(N:ℝ)*(log 64+2*log (3*((d:ℝ)+4))+A+B)+
        (64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ*Δ := by
  let E : ℝ:=∑ x,p.mass x*((bothExpensive (twoMask (Nat.card K) (F x))).card:ℝ)
  have hE0 : 0≤E:=sum_nonneg (fun x _=>mul_nonneg (p.nonneg x) (Nat.cast_nonneg _))
  have hEN : E≤N := by
    calc
      _ ≤ ∑ x,p.mass x*(N:ℝ) := by
        apply sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
        exact_mod_cast (show (bothExpensive (twoMask (Nat.card K) (F x))).card≤N by
          simpa only [Fintype.card_fin] using card_le_univ (bothExpensive (twoMask (Nat.card K) (F x))))
      _ = _ := by rw [←sum_mul,p.total,one_mul]
  have hEE : E≤(64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ := by
    calc
      _ ≤ ∑ x,p.mass x*(expensiveBudget K V+expensiveBudget K (Module.Dual K V)) := by
        exact sum_le_sum (fun x _=>mul_le_mul_of_nonneg_left (two_expensive_bound (F x)) (p.nonneg x))
      _ = _ := by rw [←sum_mul,p.total,one_mul]
      _ ≤ _ := twoExpensive_linear hdim hlog hσ
  have hJ0 : jointJ K (d+2)=log 64+((d+2:ℕ):ℝ)*σ := by
    have hq : (0:ℝ)<Nat.card K:=by exact_mod_cast Finite.card_pos
    unfold jointJ
    rw [log_mul (by norm_num) (pow_ne_zero _ hq.ne'),log_pow,hlog]
  have hcost : E*(Jprev-jointJ K (d+2))≤
      (64*((d:ℝ)+4)^3)*(Nat.card K:ℝ)*σ*Δ+(N:ℝ)*B := by
    calc
      _ ≤ E*(Δ+B) := mul_le_mul_of_nonneg_left hJ hE0
      _ = E*Δ+E*B := mul_add _ _ _
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hEE hΔ) (mul_le_mul_of_nonneg_right hEN hB)
  unfold excessCost
  rw [twoMask_log_card hdim,hJ0]
  change _ + E*(Jprev-(log 64+((d+2:ℕ):ℝ)*σ))≤_
  rw [hJ0] at hcost
  nlinarith only [hC,hF,hcost]
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Real
noncomputable section

lemma packing_bounds (m L : ℕ) (hL : 0 < L) (hm : 2*L ≤ m) :
    1 ≤ m/L ∧ (m/L)*L ≤ m ∧ (m:ℝ)/2 ≤ ((m/L)*L:ℕ) := by
  have hw : 1 ≤ m/L := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hlt:=Nat.mod_lt m hL
  have he:=Nat.mod_add_div m L
  have hl:=(Nat.div_mul_le_self m L)
  refine ⟨hw,hl,?_⟩
  have hv : m ≤ 2*((m/L)*L) := by
    have hh : L ≤ (m/L)*L:=by nlinarith
    nlinarith
  have hv' : (m:ℝ) ≤ 2*((m/L)*L:ℕ):=by exact_mod_cast hv
  linarith

end
end SharpLogRamsey.Selection.Windows

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

 attribute [local instance] OAI.SharpLogRamsey.Marking.selectProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.selectDualProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.selectDoubleProjective
theorem eventually_selected_step (i : ℕ) (η c C C0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω Γ : Type) [Fintype Ω] [Fintype Γ] (N m : ℕ) (p : Law Ω) (Cmsg : Ω→Γ)
      (F : Ω→Fin N→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
      (S : Γ→Fin N→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
      (D J : ℝ) (R : ℕ), Admissible σ η D R →
      c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (Cmsg x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      ((classCount i*m:ℕ):ℝ)+expensiveBudget (ZMod q) (Fin (i+4)→ZMod q)+
        expensiveBudget (ZMod q) (Module.Dual (ZMod q) (Fin (i+4)→ZMod q)) ≤ N →
      excessCost p Cmsg F J (jointJ (ZMod q) (i+3)) ≤
        (C0*(m:ℝ)*D*σ^(-beta η))/(classCount i:ℝ) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin N=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ C0*σ) →
      ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
        Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(N:ℝ)) (4*classCount i)) := by
  filter_upwards [eventually_class_step i η c C C0 hη hηu hc hC hC0,
    eventually_ge_atTop (1:ℝ)] with σ hstep hσ
  intro q _ hq he Ω Γ _ _ N m p Cmsg F S D J R had hmlo hmhi hSJ hS hf hcon hpack hexc hocc
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hD : 0 ≤ D:=(rpow_nonneg hσ0.le _).trans had.D_lower
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+1)+3:=by simp
  have hgap : 0 ≤ scaleKstar σ η D:=by unfold scaleKstar;positivity
  obtain ⟨cl,E,hE,T,hmn,hprob,hcard,hgcon,hgf,hG,hdef⟩:=
    actual_ordered_class hdim hgap p Cmsg F S J hcon hf hS hSJ m hpack
  let θ:=sourceMessage Cmsg F
  let p':=p.onContextEvent θ E hE
  let e:=chosenOrder T hmn
  let G:=orderedTuple T hmn θ F
  let S':=fun z j=>cheapBoth z (e z j)
  let J':=jointJ (ZMod q) (i+3)
  let budget:=excessCost p Cmsg F J J'/(p.map θ).event E
  have hK : (0:ℝ) < classCount i:=by exact_mod_cast classCount_pos i
  have hp : 1/(classCount i:ℝ) ≤ (p.map θ).event E:=hprob
  have hcost0 : 0 ≤ C0*(m:ℝ)*D*σ^(-beta η):=by positivity
  have hbudget : budget ≤ C0*(m:ℝ)*D*σ^(-beta η) := by
    apply (div_le_iff₀ hE).mpr
    calc
      _ ≤ (C0*(m:ℝ)*D*σ^(-beta η))/(classCount i:ℝ):=hexc
      _ = (C0*(m:ℝ)*D*σ^(-beta η))*(1/(classCount i:ℝ)):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hp hcost0
  have hocc' : ∀ x,p'.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j : Fin m=>covectorTuple (G x) j∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ C0*σ := by
    intro x hx W
    have hh:=count_injective_restriction (e (θ x)).toEmbedding
      (fun j=>covectorTuple (F x) j∈orthogonalRectangle Projectivization.rep Projectivization.rep W)
    apply le_trans _ (hocc x (p.onContextEvent_support θ E hE x hx).1 W)
    have heq : ∀ j,covectorTuple (G x) j=covectorTuple (F x) (e (θ x) j) := fun _=>rfl
    simp_rw [heq]
    convert (Nat.cast_le (α:=ℝ)).mpr hh using 1
    all_goals try with_reducible_and_instances rfl
    congr!
    congr 2
    ext index
    simp only [orthogonalRectangle,mem_filter,mem_univ,true_and]
  have hJ : ((i+3:ℕ):ℝ)*σ ≤ J':=by
    have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
    dsimp only [J',jointJ]
    rw [Nat.card_zmod,log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow,←he,log_exp]
    linarith [log_nonneg (by norm_num : (1:ℝ) ≤ 64)]
  obtain ⟨m',hmret,⟨out⟩⟩:=hstep q hq he Ω _ m p' θ G S' D J' (C0*σ) budget R cl
    had hmlo hmhi hJ (by positivity) le_rfl
    (fun z j=>cheapBoth_log_card hdim z (e z j)) (fun x hx j=>(hG x hx j).1)
    hgf hgcon (fun x hx j=>(hG x hx j).2)
    (fun z j=>by simpa only [Nat.card_zmod] using cheapBoth_card hdim z (e z j))
    hdef hbudget hocc'
  have hdom : ∀ x,p'.mass x ≤ (classCount i:ℝ)*p.mass x:=by
    intro x
    have hh:=p.onContextEvent_domination p θ E hE 1 (by intro x;simp) x
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (p.nonneg x)
    apply (div_le_iff₀ hE).mpr
    have hh:=(div_le_iff₀ hK).mp hp
    linarith
  have out':=out.rebase p (by norm_num) hdom
  have full:=out'.transport (Equiv.refl _) F (fun x=>e (θ x)) (fun _ _=>rfl)
  refine ⟨m',hmret,⟨full.mono (le_refl _) ?_ (le_refl _)⟩⟩
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (by positivity)
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_StageBudget
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

lemma stage_normalized {σ η Λ Δ : ℝ} {k : ℕ} (hσ : 0 < σ) :
    stageD σ η k Λ Δ*σ^(-beta η)=1+Λ/(k:ℝ)+Δ*σ^(-η) := by
  unfold stageD
  rw [mul_right_comm,←rpow_add hσ,add_neg_cancel,rpow_zero,one_mul]

lemma stage_budget_bound {σ η Λ Δ q c A E : ℝ} {k N : ℕ}
    (hσ : 0 < σ) (hk : 0 < k) (hΛ : 0 ≤ Λ) (hΔ : 0 ≤ Δ)
    (hq : 0 < q) (hc : 0 < c) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hkup : (k:ℝ) ≤ q*σ^(1+η)) (hNlo : c*q*σ^(1+η) ≤ N) :
    Λ+(N:ℝ)*A+E*q*σ*Δ ≤
      ((1+E)/c+A)*(N:ℝ)*(stageD σ η k Λ Δ*σ^(-beta η)) := by
  let Dn:=stageD σ η k Λ Δ*σ^(-beta η)
  have hkn : (0:ℝ) < k:=by exact_mod_cast hk
  have hNorm : Dn=1+Λ/(k:ℝ)+Δ*σ^(-η):=stage_normalized hσ
  have hl0 : 0 ≤ Λ/(k:ℝ):=div_nonneg hΛ hkn.le
  have hd0 : 0 ≤ Δ*σ^(-η):=by positivity
  have hDn : 1 ≤ Dn:=by rw [hNorm];linarith
  have hl : Λ ≤ (k:ℝ)*Dn := by
    have h:=mul_le_mul_of_nonneg_left (show Λ/(k:ℝ) ≤ Dn by rw [hNorm];linarith) hkn.le
    rwa [mul_div_cancel₀ Λ hkn.ne'] at h
  have hdel : Δ*σ^(-η) ≤ Dn:=by rw [hNorm];linarith
  have hcancel : σ^(-η)*σ^(1+η)=σ := by
    rw [←rpow_add hσ,show -η+(1+η)=(1:ℝ) by ring,rpow_one]
  have hdel' : q*σ*Δ ≤ q*σ^(1+η)*Dn := by
    have hh:=mul_le_mul_of_nonneg_left hdel (by positivity : 0 ≤ q*σ^(1+η))
    have heq : q*σ^(1+η)*(Δ*σ^(-η))=q*σ*Δ := by
      calc
        _ = q*Δ*(σ^(-η)*σ^(1+η)):=by ring
        _ = _:=by rw [hcancel];ring
    rwa [heq] at hh
  have hN : q*σ^(1+η) ≤ (N:ℝ)/c := (le_div_iff₀ hc).mpr (by nlinarith only [hNlo])
  have hΛN : Λ ≤ ((N:ℝ)/c)*Dn:=hl.trans (mul_le_mul_of_nonneg_right (hkup.trans hN) (by linarith))
  have hΔN : E*q*σ*Δ ≤ E*((N:ℝ)/c)*Dn := by
    have hh:=mul_le_mul_of_nonneg_left (hdel'.trans (mul_le_mul_of_nonneg_right hN (by linarith))) hE
    nlinarith only [hh]
  have hAN : (N:ℝ)*A ≤ (N:ℝ)*A*Dn:=le_mul_of_one_le_right (by positivity) hDn
  calc
    _ ≤ ((N:ℝ)/c)*Dn+(N:ℝ)*A*Dn+E*((N:ℝ)/c)*Dn:=by linarith
    _ = _:=by ring

lemma class_budget_scale {B Dn x : ℝ} {K N m : ℕ}
    (hK : 0 < K) (hB : 0 ≤ B) (hDn : 0 ≤ Dn)
    (hNm : N ≤ 4*K*m) (hx : x ≤ B*(N:ℝ)*Dn) :
    x ≤ ((4*(K:ℝ)^2*B)*(m:ℝ)*Dn)/(K:ℝ) := by
  have hk : (0:ℝ) < K:=by exact_mod_cast hK
  calc
    x ≤ B*(N:ℝ)*Dn:=hx
    _ ≤ B*(4*(K:ℝ)*m)*Dn:=by gcongr;exact_mod_cast hNm
    _ = _:=by field_simp

theorem eventually_class_packing (η c Ecoef : ℝ) (K : ℕ)
    (hη : 0 < η) (hc : 0 < c) (_hE : 0 ≤ Ecoef) (hK : 0 < K) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℝ) (N : ℕ), exp σ=q →
      c*q*σ^(1+η) ≤ N →
      let m:=N/(2*K)
      0 < m ∧ N ≤ 4*K*m ∧ K*m ≤ N ∧
      ((K*m:ℕ):ℝ)+Ecoef*q*σ ≤ N ∧
      (c/(4*K))*q*σ^(1+η) ≤ m := by
  have ht:=tendsto_rpow_atTop hη
  filter_upwards [ht.eventually_ge_atTop (max (2*Ecoef/c) (4*K/c)),
    eventually_ge_atTop (1:ℝ)] with σ hh hσ q N he hN
  have hσ0 : 0 < σ:=by linarith
  have hq : 1 ≤ q:=by rw [←he];exact one_le_exp hσ0.le
  have hq0 : 0 < q:=by linarith
  have ha : σ^(1+η)=σ*σ^η:=by rw [rpow_add hσ0,rpow_one]
  have hlarge : (4*(K:ℝ)) ≤ c*q*σ^(1+η) := by
    have hh':=(div_le_iff₀ hc).mp ((le_max_right _ _).trans hh)
    have hqs : 1 ≤ q*σ:=by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hσ)]
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left hqs (by positivity : 0 ≤ c*σ^η)]
  have hNbig : 2*(2*K) ≤ N := by
    have hh : 4*K ≤ N := by exact_mod_cast hlarge.trans hN
    omega
  obtain ⟨hm,hpack,hhalf⟩:=Selection.Windows.packing_bounds N (2*K) (by omega) hNbig
  have hNm : N ≤ 4*K*(N/(2*K)) := by
    have hh : (N:ℝ) ≤ 2*((N/(2*K))*(2*K):ℕ):=by linarith
    push_cast at hh
    exact_mod_cast (show (N:ℝ) ≤ 4*K*(N/(2*K):ℕ) by nlinarith only [hh])
  have hKm : K*(N/(2*K)) ≤ N := by nlinarith only [hpack]
  refine ⟨by omega,hNm,hKm,?_,?_⟩
  · have hec : 2*Ecoef*q*σ ≤ c*q*σ^(1+η):=by
      have hh':=(div_le_iff₀ hc).mp ((le_max_left _ _).trans hh)
      rw [ha]
      nlinarith [mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ q*σ)]
    have hh : ((N/(2*K))*(2*K):ℕ) ≤ (N:ℝ):=by exact_mod_cast hpack
    push_cast at hh ⊢
    linarith
  · have hn : (N:ℝ) ≤ 4*(K:ℝ)*(N/(2*K):ℕ):=by exact_mod_cast hNm
    apply (mul_le_mul_iff_right₀ (show (0:ℝ) < 4*K by positivity)).mp
    have heq : ((c/(4*K))*q*σ^(1+η))*(4*K)=c*q*σ^(1+η):=by field_simp
    nlinarith only [heq,hN,hn]
end
end SharpLogRamsey.SourceScales

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
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_UniformStep
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

attribute [local instance] OAI.SharpLogRamsey.Marking.uniformProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.uniformDualProjective
theorem eventually_uniform_step (i : ℕ) (η c C A B M0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM0 : 0 ≤ M0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω Γ : Type) [Fintype Ω] [Fintype Γ] (N k : ℕ) (p : Law Ω) (msg : Ω→Γ)
      (F : Ω→Fin N→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
      (S : Γ→Fin N→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
      (Λ Δ J : ℝ) (R : ℕ),
      0 < k → 0 ≤ Λ → 0 ≤ Δ → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      c*(q:ℝ)*σ^(1+η) ≤ N → (N:ℝ) ≤ C*q*σ^(1+η) →
      Admissible σ η (stageD σ η k Λ Δ) R →
      entropy (p.map msg) ≤ Λ →
      (N:ℝ)*((i+3:ℕ):ℝ)*σ-A*N ≤ entropy (p.map F) →
      J-jointJ (ZMod q) (i+3) ≤ Δ+B →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (msg x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin N=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
      ∃ m' : ℕ, (N:ℝ)/(256*classCount i) ≤ m' ∧
        Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)))
          (stageD σ η k Λ Δ*σ^(-η/3)*(N:ℝ)) (4*classCount i)) := by
  let K:=classCount i
  let Ecoef:=64*(((i+1:ℕ):ℝ)+4)^3
  let A1:=log 64+2*log (3*(((i+1:ℕ):ℝ)+4))+A+B
  let B1:=(1+Ecoef)/c+A1
  let C0:=max M0 (4*(K:ℝ)^2*B1)+1
  have hK : 0 < K:=classCount_pos i
  have hKr : (0:ℝ) < K:=by exact_mod_cast hK
  have hE : 0 ≤ Ecoef:=by dsimp only [Ecoef];positivity
  have hA1 : 0 ≤ A1:=by
    have hl : (1:ℝ) ≤ 3*(((i+1:ℕ):ℝ)+4):=by
      have : (0:ℝ) ≤ (i+1:ℕ):=by positivity
      nlinarith
    dsimp only [A1]
    linarith [log_nonneg hl,log_nonneg (by norm_num : (1:ℝ) ≤ 64)]
  have hB1 : 0 ≤ B1:=by dsimp only [B1];positivity
  have hC0 : 0 < C0:=by dsimp only [C0];linarith [le_max_left M0 (4*(K:ℝ)^2*B1)]
  have hMup : M0 ≤ C0:=by dsimp only [C0];linarith [le_max_left M0 (4*(K:ℝ)^2*B1)]
  have hCostup : 4*(K:ℝ)^2*B1 ≤ C0:=by dsimp only [C0];linarith [le_max_right M0 (4*(K:ℝ)^2*B1)]
  filter_upwards [eventually_selected_step i η (c/(4*K)) C C0 hη hηu (by positivity) hC hC0,
    eventually_class_packing η c Ecoef K hη hc hE hK,
    eventually_ge_atTop (1:ℝ)] with σ hstep hpack hσ
  intro q _ hq he Ω Γ _ _ N k p msg F S Λ Δ J R hk hΛ hΔ hkup hNlo hNhi had hmsg hF hJ hSJ hS hf hcon hocc
  have hσ0 : 0 < σ:=by linarith
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+1)+3:=by simp
  let D:=stageD σ η k Λ Δ
  let Dn:=D*σ^(-beta η)
  have hDn : 0 ≤ Dn:=by dsimp only [Dn,D,stageD];positivity
  let m:=N/(2*K)
  obtain ⟨hm,hNm,hKm,hpacking,hmlo⟩:=hpack (q:ℝ) N he hNlo
  have hmhi : (m:ℝ) ≤ C*q*σ^(1+η):=
    (show (m:ℝ) ≤ N by exact_mod_cast Nat.div_le_self N (2*K)).trans hNhi
  have hx:=excessCost_linear hdim p msg F σ Λ Δ A B J hlog hσ hΔ hB hmsg hF hJ
  rw [Nat.card_zmod] at hx
  have hxb := stage_budget_bound hσ0 hk hΛ hΔ hq0 hc hA1 hE hkup hNlo
  have hcb := class_budget_scale hK hB1 hDn hNm (hx.trans hxb)
  have hcb' : excessCost p msg F J (jointJ (ZMod q) (i+3)) ≤
      C0*(m:ℝ)*D*σ^(-beta η)/(K:ℝ) := by
    apply hcb.trans
    calc
      _ = (4*(K:ℝ)^2*B1)*((m:ℝ)*Dn/(K:ℝ)):=by ring
      _ ≤ C0*((m:ℝ)*Dn/(K:ℝ)):=mul_le_mul_of_nonneg_right hCostup (by positivity)
      _ = _:=by dsimp only [Dn];ring
  have hpacking' : ((classCount i*m:ℕ):ℝ)+
      expensiveBudget (ZMod q) (Fin (i+4)→ZMod q)+
      expensiveBudget (ZMod q) (Module.Dual (ZMod q) (Fin (i+4)→ZMod q)) ≤ N := by
    have hh:=twoExpensive_linear hdim hlog hσ
    rw [Nat.card_zmod] at hh
    dsimp only [Ecoef] at hpacking
    linarith only [hh,hpacking]
  obtain ⟨m',hmret,⟨out⟩⟩:=hstep q hq he Ω Γ N m p msg F S D J R had hmlo hmhi
    hSJ hS hf hcon hpacking' hcb' (by
      intro x hx W
      exact (hocc x hx W).trans (mul_le_mul_of_nonneg_right hMup hσ0.le))
  refine ⟨m',?_,⟨out⟩⟩
  have hn : (N:ℝ) ≤ 4*K*m:=by exact_mod_cast hNm
  apply (div_le_iff₀ (show (0:ℝ) < 256*K by positivity)).mpr
  nlinarith only [hn,hmret]
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

lemma ContextOutput.tracked_linear [Nonempty α] {β : Type} [Fintype β] {N n m : ℕ}
    {H : Ω→Fin n→β} (e : ContextOutput p H m B C L)
    (stream : Ω→Fin N→α) (F : Ω→Fin n→α)
    (φ : α→β) (hφ : Function.Injective φ) (hH : ∀ x i,H x i=φ (F x i))
    {d : ℕ} (hd : 1 ≤ d) (hm : 0 < m) (hn : n ≤ N)
    {D q σ η c : ℝ} (hD : 0 < D) (hL : 0 < L) (hq : 0 < q) (hσ : 1 ≤ σ)
    (hη : 0 ≤ η) (hc : 0 < c)
    (hdom : ∀ g,(p.map stream).mass g ≤ D/(Fintype.card α:ℝ)^N)
    (hselect : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x))
    (hsize : (N:ℝ) ≤ q^d*σ) (hlength : c*q*σ^(1+η) ≤ m)
    (halphabet : q^(2*d-1) ≤ (Fintype.card α:ℝ)) :
    (m:ℝ)*((d:ℝ)*log q)-(1+|log c|+|log (2*(L*D))|)*m ≤
      entropy (e.μ.map (fun x i=>H (e.source x) (e.chosen x i))) := by
  have hh:=e.tracked_entropy stream F φ hφ hH hd hm hn hD hL hq (by linarith) hc
    hdom hselect hsize hlength halphabet
  have hpos : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hgain : 0 ≤ (m:ℝ)*(η*log σ):=mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hη (log_nonneg hσ))
  have hm' : |log (2*(L*D))| ≤ (m:ℝ)*|log (2*(L*D))|:=le_mul_of_one_le_left (abs_nonneg _) hpos
  have hc':=mul_le_mul_of_nonneg_left (neg_abs_le (log c)) (Nat.cast_nonneg m)
  nlinarith only [hh,hgain,hm',hc',le_abs_self (log (2*(L*D)))]
end
end SharpLogRamsey.Selection

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

lemma flag_context_linear (i q : ℕ) [Fact q.Prime] (σ η c Lstar : ℝ)
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
    (m:ℝ)*((i+3:ℕ):ℝ)*σ-(1+|log c|+|log (2*(Lstar*2))|)*m ≤
      entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) := by
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hm : 0 < m:=by
    have : (0:ℝ) < m:=(by positivity : (0:ℝ) < c*(q:ℝ)*σ^(1+η)).trans_le hmlo
    exact_mod_cast this
  have halphabet:=flag_alphabet_lower i q
  have : Nonempty (Flag (ZMod q) (Fin (i+4)→ZMod q)):=Fintype.card_pos_iff.mp (by
    have : (0:ℝ) < (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ):=(pow_pos hq0 _).trans_le halphabet
    exact_mod_cast this)
  let ee:=e.mono (le_refl _) (le_refl _) hLL
  have hh:=ee.tracked_linear stream F flagPair flagPair_injective (by intros;rfl)
    (by omega : 1 ≤ i+3) hm hkn (by norm_num : (0:ℝ) < 2) hLs hq0 hσ hη hc
    hdom hselect hN hmlo halphabet
  have hlogq : log (q:ℝ)=σ:=by rw [←he,log_exp]
  rw [hlogq] at hh
  dsimp only [ee,ContextOutput.mono] at hh
  convert hh using 1 <;> first | ring | congr!

lemma flag_context_occ (i q : ℕ) [Fact q.Prime]
    (Ω : Type) [Fintype Ω] (k m : ℕ) (p : Law Ω)
    (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q)) (B Λ L M : ℝ)
    (hocc : ∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M)
    (e : ContextOutput p (fun x j=>flagPair (F x j)) m B Λ L) :
    ∀ x,e.μ.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j=>covectorTuple (fun j=>flagPair (F (e.source x) (e.chosen x j))) j∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M := by
  intro x _ W
  have hh:=count_injective_restriction (e.chosen x).toEmbedding
    (fun j=>(flagPair (F (e.source x) j)).swap∈orthogonalRectangle Projectivization.rep Projectivization.rep W)
  apply le_trans _ (hocc _ (e.supported x) W)
  convert (Nat.cast_le (α:=ℝ)).mpr hh using 1
  all_goals try with_reducible_and_instances rfl
  congr!
  congr 2
  ext index
  simp only [orthogonalRectangle,mem_filter,mem_univ,true_and]

theorem eventually_tracked_step_oai (i : ℕ) (η c Lstar P M0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hLs : 0 < Lstar)
    (hP : 1 ≤ P) (hPs : stepPrefactor (i+3) ≤ P) (hM0 : 0 ≤ M0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
      (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (Λ Δ L : ℝ) (R : ℕ),
      0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      0 ≤ Λ → 0 ≤ Δ → 0 < L → L ≤ Lstar →
      Admissible σ η (stageD σ η k Λ Δ) R →
      (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
      (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
      (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
      (e : ContextOutput p (fun x j=>flagPair (F x j)) m
        (P*(q:ℝ)^(i+3)*exp Δ) Λ L) → c*(q:ℝ)*σ^(1+η) ≤ m →
      ∃ m' : ℕ, (m:ℝ)/(256*classCount i) ≤ m' ∧
        Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m'
          (P*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)))
          (stageD σ η k Λ Δ*σ^(-η/3)*(k:ℝ)) ((4*classCount i)*L)) := by
  let A:=1+|log c|+|log (2*(Lstar*2))|
  let B:=|log P|+|log 64|
  have hA : 0 ≤ A:=by dsimp [A];positivity
  have hB : 0 ≤ B:=by dsimp [B];positivity
  filter_upwards [eventually_uniform_step i η c 1 A B M0 hη hηu hc (by norm_num) hA hB hM0,
    eventually_ge_atTop (1:ℝ)] with σ hstep hσ
  intro q _ hq he Ω _ N k m p stream F Λ Δ L R hk hkn hku hΛ hΔ hL hLL had hdom hselect hN hcon hocc e hmlo
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hF:=flag_context_linear i q σ η c Lstar hσ hη.le hc hLs he Ω N k m p stream F
    _ Λ L hLL hkn hdom hselect hN e hmlo
  let G:=fun x j=>flagPair (F (e.source x) (e.chosen x j))
  let J:=log P+((i+3:ℕ):ℝ)*σ+Δ
  obtain ⟨hJ0,hBJ,hJgap⟩:=tracked_log_budget i q σ Δ P hσ0.le hΔ hP he
  have hcons : ∀ x,e.μ.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=by
    intro x _
    exact scanConsistent_ordered _ (hcon _ (e.supported x)) (e.chosen x)
  have hocc':=flag_context_occ i q Ω k m p F _ Λ L (M0*σ) hocc e
  obtain ⟨m',hmret,⟨out⟩⟩:=hstep q hq he e.X e.Γ m k e.μ e.msg G e.domains Λ Δ J R
    hk hΛ hΔ hku hmlo (by simpa only [one_mul] using (show (m:ℝ) ≤ k by exact_mod_cast e.length_le).trans hku)
    had e.cost hF hJgap (e.log_size hJ0 hBJ)
    (fun x _ j=>e.hit x j) (fun x _ j=>(F (e.source x) (e.chosen x j)).incident) hcons hocc'
  have hs : stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)) ≤
      P*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)):=by gcongr
  have hcost : stageD σ η k Λ Δ*σ^(-η/3)*(m:ℝ) ≤ stageD σ η k Λ Δ*σ^(-η/3)*(k:ℝ):=by
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast e.length_le)
    unfold stageD
    positivity
  exact ⟨m',hmret,⟨e.compose (out.mono hs hcost (le_refl _)) (by positivity)⟩⟩
end
end SharpLogRamsey.Marking

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Marking.eventually_tracked_step_oai := @OAI.SharpLogRamsey.Marking.eventually_tracked_step_oai
