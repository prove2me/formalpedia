-- Prove2me | solution 1 for GibbsCongestion.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:58:36.108176+00:00
-- url     : https://prove2.me/submissions/32433900-bc4f-4d7a-9d4e-71e81853c7f0

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_loadPotential
set_option autoImplicit false

namespace Aux_GC41

open GibbsCongestion

section General

variable {E : Type*} [DecidableEq E]

def dec (a : Finset E → ℕ) (u : Finset E) : Finset E → ℕ := Function.update a u (a u - 1)

def inc (a : Finset E → ℕ) (u : Finset E) : Finset E → ℕ := Function.update a u (a u + 1)

/-- Lifted exchange property (M-convexity of the lift to `Q ∪ {0}`). -/
def EX (Q : Finset (Finset E)) (g : (Finset E → ℕ) → ℝ) : Prop :=
  (∀ a b : Finset E → ℕ, ∀ u ∈ Q, b u < a u →
    (∃ v ∈ Q, a v < b v ∧ g (inc (dec a u) v) + g (inc (dec b v) u) ≤ g a + g b) ∨
    (∑ q ∈ Q, b q < ∑ q ∈ Q, a q ∧ g (dec a u) + g (inc b u) ≤ g a + g b)) ∧
  (∀ a b : Finset E → ℕ, ∑ q ∈ Q, a q < ∑ q ∈ Q, b q →
    ∃ v ∈ Q, a v < b v ∧ g (inc a v) + g (dec b v) ≤ g a + g b)

/-- `g` only reads the coordinates in `Q`. -/
def Cg (Q : Finset (Finset E)) (g : (Finset E → ℕ) → ℝ) : Prop :=
  ∀ a b : Finset E → ℕ, (∀ q ∈ Q, a q = b q) → g a = g b

theorem inc_self (a : Finset E → ℕ) (u : Finset E) : inc a u u = a u + 1 := by
  unfold inc; exact Function.update_self u _ a

theorem dec_self (a : Finset E → ℕ) (u : Finset E) : dec a u u = a u - 1 := by
  unfold dec; exact Function.update_self u _ a

theorem inc_ne (a : Finset E → ℕ) (u q : Finset E) (h : q ≠ u) : inc a u q = a q := by
  unfold inc; exact Function.update_of_ne h _ a

theorem dec_ne (a : Finset E → ℕ) (u q : Finset E) (h : q ≠ u) : dec a u q = a q := by
  unfold dec; exact Function.update_of_ne h _ a

theorem sum_inc (Q : Finset (Finset E)) (a : Finset E → ℕ) (u : Finset E) (hu : u ∈ Q) :
    ∑ q ∈ Q, inc a u q = ∑ q ∈ Q, a q + 1 := by
  rw [← Finset.add_sum_erase Q _ hu, ← Finset.add_sum_erase Q a hu]
  have h : ∑ q ∈ Q.erase u, inc a u q = ∑ q ∈ Q.erase u, a q :=
    Finset.sum_congr rfl (fun q hq => inc_ne a u q (Finset.ne_of_mem_erase hq))
  rw [h, inc_self]
  ring

theorem sum_dec (Q : Finset (Finset E)) (a : Finset E → ℕ) (u : Finset E) (hu : u ∈ Q)
    (h1 : 1 ≤ a u) : ∑ q ∈ Q, dec a u q + 1 = ∑ q ∈ Q, a q := by
  rw [← Finset.add_sum_erase Q _ hu, ← Finset.add_sum_erase Q a hu]
  have h : ∑ q ∈ Q.erase u, dec a u q = ∑ q ∈ Q.erase u, a q :=
    Finset.sum_congr rfl (fun q hq => dec_ne a u q (Finset.ne_of_mem_erase hq))
  rw [h, dec_self]
  omega

theorem conv_step (F : ℕ → ℝ) (hF : ∀ x y : ℕ, x ≤ y → F (x + 1) - F x ≤ F (y + 1) - F y)
    (x y : ℕ) (hxy : x ≤ y) : F (x + 1) + F y ≤ F x + F (y + 1) := by
  have := hF x y hxy
  linarith

theorem ex_base (F : ℕ → ℝ) (hF : ∀ x y : ℕ, x ≤ y → F (x + 1) - F x ≤ F (y + 1) - F y)
    (p : Finset E) : EX {p} (fun a => F (a p)) := by
  constructor
  · intro a b u hu hba
    have hup : u = p := Finset.mem_singleton.mp hu
    rw [hup] at hba ⊢
    right
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_singleton, Finset.sum_singleton]
      exact hba
    · show F (dec a p p) + F (inc b p p) ≤ F (a p) + F (b p)
      rw [dec_self, inc_self]
      have h := conv_step F hF (b p) (a p - 1) (by omega)
      have e : a p - 1 + 1 = a p := by omega
      rw [e] at h
      linarith
  · intro a b hab
    rw [Finset.sum_singleton, Finset.sum_singleton] at hab
    refine ⟨p, Finset.mem_singleton_self p, hab, ?_⟩
    show F (inc a p p) + F (dec b p p) ≤ F (a p) + F (b p)
    rw [dec_self, inc_self]
    have h := conv_step F hF (a p) (b p - 1) (by omega)
    have e : b p - 1 + 1 = b p := by omega
    rw [e] at h
    linarith

theorem cg_add_total (Q : Finset (Finset E)) (g : (Finset E → ℕ) → ℝ) (F : ℕ → ℝ)
    (hcg : Cg Q g) : Cg Q (fun a => g a + F (∑ q ∈ Q, a q)) := by
  intro a b hab
  show g a + F (∑ q ∈ Q, a q) = g b + F (∑ q ∈ Q, b q)
  rw [hcg a b hab, Finset.sum_congr rfl hab]

theorem ex_add_total (Q : Finset (Finset E)) (g : (Finset E → ℕ) → ℝ) (F : ℕ → ℝ)
    (hF : ∀ x y : ℕ, x ≤ y → F (x + 1) - F x ≤ F (y + 1) - F y) (hex : EX Q g) :
    EX Q (fun a => g a + F (∑ q ∈ Q, a q)) := by
  constructor
  · intro a b u hu hba
    rcases hex.1 a b u hu hba with ⟨v, hv, hav, hg⟩ | ⟨hs, hg⟩
    · left
      refine ⟨v, hv, hav, ?_⟩
      have s1 : ∑ q ∈ Q, inc (dec a u) v q = ∑ q ∈ Q, a q := by
        rw [sum_inc Q _ v hv]
        exact sum_dec Q a u hu (by omega)
      have s2 : ∑ q ∈ Q, inc (dec b v) u q = ∑ q ∈ Q, b q := by
        rw [sum_inc Q _ u hu]
        exact sum_dec Q b v hv (by omega)
      show g (inc (dec a u) v) + F (∑ q ∈ Q, inc (dec a u) v q) +
          (g (inc (dec b v) u) + F (∑ q ∈ Q, inc (dec b v) u q)) ≤
        g a + F (∑ q ∈ Q, a q) + (g b + F (∑ q ∈ Q, b q))
      rw [s1, s2]
      linarith
    · right
      refine ⟨hs, ?_⟩
      have hd := sum_dec Q a u hu (by omega)
      have hi := sum_inc Q b u hu
      show g (dec a u) + F (∑ q ∈ Q, dec a u q) + (g (inc b u) + F (∑ q ∈ Q, inc b u q)) ≤
        g a + F (∑ q ∈ Q, a q) + (g b + F (∑ q ∈ Q, b q))
      rw [hi, ← hd]
      have hc := conv_step F hF (∑ q ∈ Q, b q) (∑ q ∈ Q, dec a u q) (by omega)
      linarith
  · intro a b hab
    obtain ⟨v, hv, hav, hg⟩ := hex.2 a b hab
    refine ⟨v, hv, hav, ?_⟩
    have hd := sum_dec Q b v hv (by omega)
    have hi := sum_inc Q a v hv
    show g (inc a v) + F (∑ q ∈ Q, inc a v q) + (g (dec b v) + F (∑ q ∈ Q, dec b v q)) ≤
      g a + F (∑ q ∈ Q, a q) + (g b + F (∑ q ∈ Q, b q))
    rw [hi, ← hd]
    have hc := conv_step F hF (∑ q ∈ Q, a q) (∑ q ∈ Q, dec b v q) (by omega)
    linarith

/-- Agreement on `Q` is preserved by `inc`/`dec` at a common point. -/
theorem agree_inc (Q : Finset (Finset E)) (f h : Finset E → ℕ) (u : Finset E) (hu : u ∈ Q)
    (hfh : ∀ q ∈ Q, f q = h q) : ∀ q ∈ Q, inc f u q = inc h u q := by
  intro q hq
  by_cases hqu : q = u
  · rw [hqu, inc_self, inc_self, hfh u hu]
  · rw [inc_ne f u q hqu, inc_ne h u q hqu]
    exact hfh q hq

theorem agree_dec (Q : Finset (Finset E)) (f h : Finset E → ℕ) (u : Finset E) (hu : u ∈ Q)
    (hfh : ∀ q ∈ Q, f q = h q) : ∀ q ∈ Q, dec f u q = dec h u q := by
  intro q hq
  by_cases hqu : q = u
  · rw [hqu, dec_self, dec_self, hfh u hu]
  · rw [dec_ne f u q hqu, dec_ne h u q hqu]
    exact hfh q hq

theorem agree_inc_out (Q : Finset (Finset E)) (f : Finset E → ℕ) (u : Finset E) (hu : u ∉ Q) :
    ∀ q ∈ Q, inc f u q = f q := by
  intro q hq
  exact inc_ne f u q (fun h => hu (h ▸ hq))

theorem agree_dec_out (Q : Finset (Finset E)) (f : Finset E → ℕ) (u : Finset E) (hu : u ∉ Q) :
    ∀ q ∈ Q, dec f u q = f q := by
  intro q hq
  exact dec_ne f u q (fun h => hu (h ▸ hq))

theorem comp_inc (Q : Finset (Finset E)) (σ : Finset E → Finset E) (hσ : Set.InjOn σ Q)
    (f : Finset E → ℕ) (u : Finset E) (hu : u ∈ Q) :
    ∀ q ∈ Q, (inc f (σ u) ∘ σ) q = inc (f ∘ σ) u q := by
  intro q hq
  by_cases hqu : q = u
  · rw [hqu]
    show inc f (σ u) (σ u) = inc (f ∘ σ) u u
    exact (inc_self f (σ u)).trans (inc_self (f ∘ σ) u).symm
  · have hne : σ q ≠ σ u := fun h => hqu (hσ hq hu h)
    show inc f (σ u) (σ q) = inc (f ∘ σ) u q
    exact (inc_ne f (σ u) (σ q) hne).trans (inc_ne (f ∘ σ) u q hqu).symm

theorem comp_dec (Q : Finset (Finset E)) (σ : Finset E → Finset E) (hσ : Set.InjOn σ Q)
    (f : Finset E → ℕ) (u : Finset E) (hu : u ∈ Q) :
    ∀ q ∈ Q, (dec f (σ u) ∘ σ) q = dec (f ∘ σ) u q := by
  intro q hq
  by_cases hqu : q = u
  · rw [hqu]
    show dec f (σ u) (σ u) = dec (f ∘ σ) u u
    exact (dec_self f (σ u)).trans (dec_self (f ∘ σ) u).symm
  · have hne : σ q ≠ σ u := fun h => hqu (hσ hq hu h)
    show dec f (σ u) (σ q) = dec (f ∘ σ) u q
    exact (dec_ne f (σ u) (σ q) hne).trans (dec_ne (f ∘ σ) u q hqu).symm

theorem comp_incdec (Q : Finset (Finset E)) (σ : Finset E → Finset E) (hσ : Set.InjOn σ Q)
    (f : Finset E → ℕ) (u v : Finset E) (hu : u ∈ Q) (hv : v ∈ Q) :
    ∀ q ∈ Q, (inc (dec f (σ u)) (σ v) ∘ σ) q = inc (dec (f ∘ σ) u) v q := by
  intro q hq
  rw [comp_inc Q σ hσ (dec f (σ u)) v hv q hq]
  exact agree_inc Q _ _ v hv (comp_dec Q σ hσ f u hu) q hq

theorem ex_reindex (Q : Finset (Finset E)) (g : (Finset E → ℕ) → ℝ) (σ : Finset E → Finset E)
    (hσ : Set.InjOn σ Q) (hcg : Cg Q g) (hex : EX Q g) :
    EX (Q.image σ) (fun a => g (a ∘ σ)) := by
  have hsum : ∀ f : Finset E → ℕ, ∑ q ∈ Q.image σ, f q = ∑ q ∈ Q, (f ∘ σ) q :=
    fun f => Finset.sum_image hσ
  constructor
  · intro a b u' hu' hba
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu'
    rcases hex.1 (a ∘ σ) (b ∘ σ) u hu hba with ⟨v, hv, hav, hg⟩ | ⟨hs, hg⟩
    · left
      refine ⟨σ v, Finset.mem_image_of_mem σ hv, hav, ?_⟩
      show g (inc (dec a (σ u)) (σ v) ∘ σ) + g (inc (dec b (σ v)) (σ u) ∘ σ) ≤
        g (a ∘ σ) + g (b ∘ σ)
      rw [hcg _ _ (comp_incdec Q σ hσ a u v hu hv), hcg _ _ (comp_incdec Q σ hσ b v u hv hu)]
      exact hg
    · right
      refine ⟨by rw [hsum, hsum]; exact hs, ?_⟩
      show g (dec a (σ u) ∘ σ) + g (inc b (σ u) ∘ σ) ≤ g (a ∘ σ) + g (b ∘ σ)
      rw [hcg _ _ (comp_dec Q σ hσ a u hu), hcg _ _ (comp_inc Q σ hσ b u hu)]
      exact hg
  · intro a b hab
    rw [hsum, hsum] at hab
    obtain ⟨v, hv, hav, hg⟩ := hex.2 (a ∘ σ) (b ∘ σ) hab
    refine ⟨σ v, Finset.mem_image_of_mem σ hv, hav, ?_⟩
    show g (inc a (σ v) ∘ σ) + g (dec b (σ v) ∘ σ) ≤ g (a ∘ σ) + g (b ∘ σ)
    rw [hcg _ _ (comp_inc Q σ hσ a v hv), hcg _ _ (comp_dec Q σ hσ b v hv)]
    exact hg

theorem cg_reindex (Q : Finset (Finset E)) (g : (Finset E → ℕ) → ℝ) (σ : Finset E → Finset E)
    (hcg : Cg Q g) : Cg (Q.image σ) (fun a => g (a ∘ σ)) := by
  intro a b hab
  show g (a ∘ σ) = g (b ∘ σ)
  exact hcg _ _ (fun q hq => hab (σ q) (Finset.mem_image_of_mem σ hq))

/-- One half of the exchange for a disjoint union: the case `u ∈ Q₁`. -/
theorem par_A (Q₁ Q₂ : Finset (Finset E)) (g₁ g₂ : (Finset E → ℕ) → ℝ)
    (hd : Disjoint Q₁ Q₂) (hc₁ : Cg Q₁ g₁) (hc₂ : Cg Q₂ g₂) (he₁ : EX Q₁ g₁) (he₂ : EX Q₂ g₂)
    (a b : Finset E → ℕ) (u : Finset E) (hu : u ∈ Q₁) (hba : b u < a u) :
    (∃ v ∈ Q₁ ∪ Q₂, a v < b v ∧
        g₁ (inc (dec a u) v) + g₂ (inc (dec a u) v) + (g₁ (inc (dec b v) u) + g₂ (inc (dec b v) u))
          ≤ g₁ a + g₂ a + (g₁ b + g₂ b)) ∨
      (∑ q ∈ Q₁ ∪ Q₂, b q < ∑ q ∈ Q₁ ∪ Q₂, a q ∧
        g₁ (dec a u) + g₂ (dec a u) + (g₁ (inc b u) + g₂ (inc b u)) ≤
          g₁ a + g₂ a + (g₁ b + g₂ b)) := by
  have hu2 : u ∉ Q₂ := Finset.disjoint_left.mp hd hu
  rcases he₁.1 a b u hu hba with ⟨v, hv, hav, hg⟩ | ⟨hs, hg⟩
  · left
    have hv2 : v ∉ Q₂ := Finset.disjoint_left.mp hd hv
    refine ⟨v, Finset.mem_union_left _ hv, hav, ?_⟩
    have ea : g₂ (inc (dec a u) v) = g₂ a := by
      apply hc₂
      intro q hq
      rw [agree_inc_out Q₂ _ v hv2 q hq, agree_dec_out Q₂ _ u hu2 q hq]
    have eb : g₂ (inc (dec b v) u) = g₂ b := by
      apply hc₂
      intro q hq
      rw [agree_inc_out Q₂ _ u hu2 q hq, agree_dec_out Q₂ _ v hv2 q hq]
    rw [ea, eb]
    linarith
  · have hsum : ∀ f : Finset E → ℕ, ∑ q ∈ Q₁ ∪ Q₂, f q = ∑ q ∈ Q₁, f q + ∑ q ∈ Q₂, f q :=
      fun f => Finset.sum_union hd
    by_cases htot : ∑ q ∈ Q₁ ∪ Q₂, b q < ∑ q ∈ Q₁ ∪ Q₂, a q
    · right
      refine ⟨htot, ?_⟩
      have ea : g₂ (dec a u) = g₂ a := hc₂ _ _ (agree_dec_out Q₂ a u hu2)
      have eb : g₂ (inc b u) = g₂ b := hc₂ _ _ (agree_inc_out Q₂ b u hu2)
      rw [ea, eb]
      linarith
    · left
      rw [hsum, hsum] at htot
      have h2 : ∑ q ∈ Q₂, a q < ∑ q ∈ Q₂, b q := by omega
      obtain ⟨v, hv, hav, hg2⟩ := he₂.2 a b h2
      have hv1 : v ∉ Q₁ := Finset.disjoint_right.mp hd hv
      refine ⟨v, Finset.mem_union_right _ hv, hav, ?_⟩
      have e1 : g₁ (inc (dec a u) v) = g₁ (dec a u) := hc₁ _ _ (agree_inc_out Q₁ _ v hv1)
      have e2 : g₁ (inc (dec b v) u) = g₁ (inc b u) := by
        apply hc₁
        intro q hq
        exact agree_inc Q₁ _ _ u hu (agree_dec_out Q₁ b v hv1) q hq
      have e3 : g₂ (inc (dec a u) v) = g₂ (inc a v) := by
        apply hc₂
        intro q hq
        exact agree_inc Q₂ _ _ v hv (agree_dec_out Q₂ a u hu2) q hq
      have e4 : g₂ (inc (dec b v) u) = g₂ (dec b v) := hc₂ _ _ (agree_inc_out Q₂ _ u hu2)
      rw [e1, e2, e3, e4]
      linarith

theorem ex_par (Q₁ Q₂ : Finset (Finset E)) (g₁ g₂ : (Finset E → ℕ) → ℝ)
    (hd : Disjoint Q₁ Q₂) (hc₁ : Cg Q₁ g₁) (hc₂ : Cg Q₂ g₂) (he₁ : EX Q₁ g₁) (he₂ : EX Q₂ g₂) :
    EX (Q₁ ∪ Q₂) (fun a => g₁ a + g₂ a) := by
  constructor
  · intro a b u hu hba
    rcases Finset.mem_union.mp hu with hu1 | hu2
    · exact par_A Q₁ Q₂ g₁ g₂ hd hc₁ hc₂ he₁ he₂ a b u hu1 hba
    · have h := par_A Q₂ Q₁ g₂ g₁ hd.symm hc₂ hc₁ he₂ he₁ a b u hu2 hba
      rw [Finset.union_comm Q₂ Q₁] at h
      rcases h with ⟨v, hv, hav, hg⟩ | ⟨hs, hg⟩
      · left
        refine ⟨v, hv, hav, ?_⟩
        show g₁ (inc (dec a u) v) + g₂ (inc (dec a u) v) +
            (g₁ (inc (dec b v) u) + g₂ (inc (dec b v) u)) ≤ g₁ a + g₂ a + (g₁ b + g₂ b)
        linarith
      · right
        refine ⟨hs, ?_⟩
        show g₁ (dec a u) + g₂ (dec a u) + (g₁ (inc b u) + g₂ (inc b u)) ≤
          g₁ a + g₂ a + (g₁ b + g₂ b)
        linarith
  · intro a b hab
    rw [Finset.sum_union hd, Finset.sum_union hd] at hab
    by_cases h1 : ∑ q ∈ Q₁, a q < ∑ q ∈ Q₁, b q
    · obtain ⟨v, hv, hav, hg⟩ := he₁.2 a b h1
      have hv2 : v ∉ Q₂ := Finset.disjoint_left.mp hd hv
      refine ⟨v, Finset.mem_union_left _ hv, hav, ?_⟩
      have ea : g₂ (inc a v) = g₂ a := hc₂ _ _ (agree_inc_out Q₂ a v hv2)
      have eb : g₂ (dec b v) = g₂ b := hc₂ _ _ (agree_dec_out Q₂ b v hv2)
      show g₁ (inc a v) + g₂ (inc a v) + (g₁ (dec b v) + g₂ (dec b v)) ≤
        g₁ a + g₂ a + (g₁ b + g₂ b)
      rw [ea, eb]
      linarith
    · have h2 : ∑ q ∈ Q₂, a q < ∑ q ∈ Q₂, b q := by omega
      obtain ⟨v, hv, hav, hg⟩ := he₂.2 a b h2
      have hv1 : v ∉ Q₁ := Finset.disjoint_right.mp hd hv
      refine ⟨v, Finset.mem_union_right _ hv, hav, ?_⟩
      have ea : g₁ (inc a v) = g₁ a := hc₁ _ _ (agree_inc_out Q₁ a v hv1)
      have eb : g₁ (dec b v) = g₁ b := hc₁ _ _ (agree_dec_out Q₁ b v hv1)
      show g₁ (inc a v) + g₂ (inc a v) + (g₁ (dec b v) + g₂ (dec b v)) ≤
        g₁ a + g₂ a + (g₁ b + g₂ b)
      rw [ea, eb]
      linarith

theorem cg_par (Q₁ Q₂ : Finset (Finset E)) (g₁ g₂ : (Finset E → ℕ) → ℝ)
    (hc₁ : Cg Q₁ g₁) (hc₂ : Cg Q₂ g₂) : Cg (Q₁ ∪ Q₂) (fun a => g₁ a + g₂ a) := by
  intro a b hab
  show g₁ a + g₂ a = g₁ b + g₂ b
  rw [hc₁ a b (fun q hq => hab q (Finset.mem_union_left _ hq)),
    hc₂ a b (fun q hq => hab q (Finset.mem_union_right _ hq))]

end General

section Pot

variable {E : Type*} [Fintype E] [DecidableEq E]

def Fc (c : E → ℕ → ℝ) (e : E) (m : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 m, c e k

def Phi (c : E → ℕ → ℝ) (P : Finset (Finset E)) (a : Finset E → ℕ) : ℝ :=
  ∑ e, Fc c e (∑ p ∈ P.filter (fun p => e ∈ p), a p)

theorem Fc_zero (c : E → ℕ → ℝ) (e : E) : Fc c e 0 = 0 := by
  unfold Fc
  rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by omega), Finset.sum_empty]

theorem Fc_succ (c : E → ℕ → ℝ) (e : E) (m : ℕ) : Fc c e (m + 1) = Fc c e m + c e (m + 1) := by
  unfold Fc
  exact Finset.sum_Icc_succ_top (by omega) _

theorem Fc_conv (c : E → ℕ → ℝ) (hc : ∀ e, Monotone (c e)) (e : E) :
    ∀ x y : ℕ, x ≤ y → Fc c e (x + 1) - Fc c e x ≤ Fc c e (y + 1) - Fc c e y := by
  intro x y hxy
  rw [Fc_succ, Fc_succ]
  have := hc e (show x + 1 ≤ y + 1 by omega)
  linarith

theorem cg_Phi (c : E → ℕ → ℝ) (P : Finset (Finset E)) : Cg P (Phi c P) := by
  intro a b hab
  unfold Phi
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_congr rfl (fun p hp => hab p (Finset.mem_filter.mp hp).1)]

theorem Phi_arc (c : E → ℕ → ℝ) (e : E) : Phi c {{e}} = fun a => Fc c e (a {e}) := by
  funext a
  unfold Phi
  rw [Finset.sum_eq_single e]
  · have h : ({{e}} : Finset (Finset E)).filter (fun p => e ∈ p) = {{e}} :=
      Finset.filter_true_of_mem (fun p hp => by
        rw [Finset.mem_singleton.mp hp]
        exact Finset.mem_singleton_self e)
    rw [h, Finset.sum_singleton]
  · intro e' _ he'
    have h : ({{e}} : Finset (Finset E)).filter (fun p => e' ∈ p) = ∅ :=
      Finset.filter_false_of_mem (fun p hp => by
        rw [Finset.mem_singleton.mp hp]
        exact fun h => he' (Finset.mem_singleton.mp h))
    rw [h, Finset.sum_empty, Fc_zero]
  · intro h
    exact absurd (Finset.mem_univ e) h

theorem Phi_par (c : E → ℕ → ℝ) (P₁ P₂ : Finset (Finset E))
    (hd : Disjoint (P₁.sup id) (P₂.sup id)) (hdisj : Disjoint P₁ P₂) :
    Phi c (P₁ ∪ P₂) = fun a => Phi c P₁ a + Phi c P₂ a := by
  funext a
  unfold Phi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]
  by_cases h1 : ∃ p ∈ P₁, e ∈ p
  · obtain ⟨p, hp, hep⟩ := h1
    have he1 : e ∈ P₁.sup id := Finset.mem_of_subset (Finset.le_sup (f := id) hp) hep
    have he2 : e ∉ P₂.sup id := Finset.disjoint_left.mp hd he1
    have hz : P₂.filter (fun p => e ∈ p) = ∅ :=
      Finset.filter_false_of_mem (fun q hq heq =>
        he2 (Finset.mem_of_subset (Finset.le_sup (f := id) hq) heq))
    rw [hz, Finset.sum_empty, Fc_zero, add_zero, add_zero]
  · push_neg at h1
    have hz : P₁.filter (fun p => e ∈ p) = ∅ := Finset.filter_false_of_mem h1
    rw [hz, Finset.sum_empty, Fc_zero, zero_add, zero_add]

theorem not_mem_of_sup (P : Finset (Finset E)) (e : E) (he : e ∉ P.sup id) :
    ∀ p ∈ P, e ∉ p :=
  fun p hp hep => he (Finset.mem_of_subset (Finset.le_sup (f := id) hp) hep)

theorem inj_insert (P : Finset (Finset E)) (e : E) (he : e ∉ P.sup id) :
    Set.InjOn (insert e) (P : Set (Finset E)) := by
  intro p hp q hq hpq
  have h1 : (insert e p).erase e = (insert e q).erase e := by rw [hpq]
  rw [Finset.erase_insert (not_mem_of_sup P e he p (Finset.mem_coe.mp hp)),
    Finset.erase_insert (not_mem_of_sup P e he q (Finset.mem_coe.mp hq))] at h1
  exact h1

theorem Phi_series (c : E → ℕ → ℝ) (P : Finset (Finset E)) (e : E) (he : e ∉ P.sup id) :
    Phi c (P.image (insert e)) =
      fun a => Phi c P (a ∘ insert e) + Fc c e (∑ q ∈ P.image (insert e), a q) := by
  have hinj := inj_insert P e he
  funext a
  have hin : ∀ e' : E, ∑ p' ∈ (P.image (insert e)).filter (fun p => e' ∈ p), a p' =
      ∑ p ∈ P.filter (fun p => e' ∈ insert e p), a (insert e p) := by
    intro e'
    rw [Finset.filter_image]
    refine Finset.sum_image (hinj.mono ?_)
    intro x hx
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
  unfold Phi
  simp only [hin, Function.comp_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e), ← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  have h1 : P.filter (fun p => e ∈ insert e p) = P :=
    Finset.filter_true_of_mem (fun p _ => Finset.mem_insert_self e p)
  have h2 : P.filter (fun p => e ∈ p) = ∅ :=
    Finset.filter_false_of_mem (not_mem_of_sup P e he)
  have h3 : ∑ p ∈ P, a (insert e p) = ∑ q ∈ P.image (insert e), a q :=
    (Finset.sum_image hinj).symm
  have h4 : ∑ e' ∈ Finset.univ.erase e,
      Fc c e' (∑ p ∈ P.filter (fun p => e' ∈ insert e p), a (insert e p)) =
      ∑ e' ∈ Finset.univ.erase e, Fc c e' (∑ p ∈ P.filter (fun p => e' ∈ p), a (insert e p)) := by
    refine Finset.sum_congr rfl (fun e' he' => ?_)
    have hne : e' ≠ e := Finset.ne_of_mem_erase he'
    have hf : P.filter (fun p => e' ∈ insert e p) = P.filter (fun p => e' ∈ p) :=
      Finset.filter_congr (fun p _ => by
        rw [Finset.mem_insert]
        exact or_iff_right hne)
    rw [hf]
  rw [h1, h2, Finset.sum_empty, Fc_zero, zero_add, h3, h4]
  ring

theorem main_ind (c : E → ℕ → ℝ) (hc : ∀ e, Monotone (c e)) (P : Finset (Finset E))
    (hP : IsEPFamily P) : EX P (Phi c P) ∧ ∀ p ∈ P, p.Nonempty := by
  induction hP with
  | arc e =>
    refine ⟨?_, ?_⟩
    · rw [Phi_arc]
      exact ex_base (Fc c e) (Fc_conv c hc e) {e}
    · intro p hp
      rw [Finset.mem_singleton.mp hp]
      exact Finset.singleton_nonempty e
  | @parallel P₁ P₂ _ _ hd ih1 ih2 =>
    have hdisj : Disjoint P₁ P₂ := by
      refine Finset.disjoint_left.mpr (fun p hp1 hp2 => ?_)
      obtain ⟨x, hx⟩ := ih1.2 p hp1
      exact Finset.disjoint_left.mp hd (Finset.mem_of_subset (Finset.le_sup (f := id) hp1) hx)
        (Finset.mem_of_subset (Finset.le_sup (f := id) hp2) hx)
    refine ⟨?_, ?_⟩
    · rw [Phi_par c P₁ P₂ hd hdisj]
      exact ex_par P₁ P₂ _ _ hdisj (cg_Phi c P₁) (cg_Phi c P₂) ih1.1 ih2.1
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact ih1.2 p h
      · exact ih2.2 p h
  | @series Q e _ he ih =>
    refine ⟨?_, ?_⟩
    · rw [Phi_series c Q e he]
      exact ex_add_total _ _ (Fc c e) (Fc_conv c hc e)
        (ex_reindex Q (Phi c Q) (insert e) (inj_insert Q e he) (cg_Phi c Q) ih.1)
    · intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.insert_nonempty e q

theorem inner_eq (P : Finset (Finset E)) (α : P → ℕ) (a : Finset E → ℕ)
    (h : ∀ p : P, a p = α p) (e : E) :
    ∑ p ∈ Finset.univ.filter (fun p : P => e ∈ (p : Finset E)), α p =
      ∑ q ∈ P.filter (fun q => e ∈ q), a q := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_coe_sort (s := P)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [h p]

theorem lp_eq (c : E → ℕ → ℝ) (P : Finset (Finset E)) (α : P → ℕ) (a : Finset E → ℕ)
    (h : ∀ p : P, a p = α p) : loadPotential c α = Phi c P a := by
  unfold loadPotential Phi Fc
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [inner_eq P α a h e]

theorem memf {α : Type*} [Fintype α] (p : α → Prop) (inst : DecidablePred p) (x : α) :
    x ∈ @Finset.filter α p inst Finset.univ ↔ p x := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Pot

end Aux_GC41

open GibbsCongestion DiscreteConvex.ConjugacyDualityD Aux_GC41 in
theorem solution {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) :
    DiscreteConvex.ConjugacyDualityD.MExchangeAxiom (fun α : P → ℤ =>
      if (∀ p, 0 ≤ α p) ∧ ∑ p, α p = (n : ℤ) then
        ((loadPotential c (fun p => (α p).toNat) : ℝ) : WithTop ℝ)
      else ⊤) := by
  obtain ⟨hEX, _⟩ := main_ind c hc_mono P hP
  have hdom : ∀ x : P → ℤ, x ∈ DomZ (fun α : P → ℤ =>
      if (∀ p, 0 ≤ α p) ∧ ∑ p, α p = (n : ℤ) then
        ((loadPotential c (fun p => (α p).toNat) : ℝ) : WithTop ℝ) else ⊤) →
      (∀ p, 0 ≤ x p) ∧ ∑ p, x p = (n : ℤ) := by
    intro x hx
    by_contra h
    have hx' : (if (∀ p, 0 ≤ x p) ∧ ∑ p, x p = (n : ℤ) then
        ((loadPotential c (fun p => (x p).toNat) : ℝ) : WithTop ℝ) else ⊤) ≠ ⊤ := hx
    exact hx' (by rw [if_neg h])
  have lift : ∀ x : P → ℤ, ∃ a : Finset E → ℕ, ∀ p : P, a p = (x p).toNat := by
    intro x
    refine ⟨fun q => if h : q ∈ P then (x ⟨q, h⟩).toNat else 0, fun p => ?_⟩
    show (if h : (p : Finset E) ∈ P then (x ⟨p, h⟩).toNat else 0) = (x p).toNat
    split_ifs with h
    · rfl
    · exact absurd p.2 h
  have hcast : ∀ g : Finset E → ℕ, ∑ p : P, ((g p : ℕ) : ℤ) = ((∑ q ∈ P, g q : ℕ) : ℤ) := by
    intro g
    rw [← Finset.sum_coe_sort (s := P) (f := g), Nat.cast_sum]
  have hsum : ∀ (x : P → ℤ) (a : Finset E → ℕ), (∀ p : P, a p = (x p).toNat) →
      (∀ p, 0 ≤ x p) → ((∑ q ∈ P, a q : ℕ) : ℤ) = ∑ p, x p := by
    intro x a ha hx0
    rw [← hcast a]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [ha p]
    exact Int.toNat_of_nonneg (hx0 p)
  intro x hx y hy u hu
  have hxd := hdom x hx
  have hyd := hdom y hy
  obtain ⟨a, ha⟩ := lift x
  obtain ⟨b, hb⟩ := lift y
  have hsa : ∑ q ∈ P, a q = n := by
    have h := hsum x a ha hxd.1
    rw [hxd.2] at h
    exact_mod_cast h
  have hsb : ∑ q ∈ P, b q = n := by
    have h := hsum y b hb hyd.1
    rw [hyd.2] at h
    exact_mod_cast h
  unfold SuppPos at hu
  have hu' : y u < x u := (memf _ _ u).mp hu
  have hxu := Int.toNat_of_nonneg (hxd.1 u)
  have hyu := Int.toNat_of_nonneg (hyd.1 u)
  have hab : b (u : Finset E) < a (u : Finset E) := by
    rw [ha u, hb u]
    omega
  rcases hEX.1 a b u u.2 hab with ⟨v, hv, hav, hg⟩ | ⟨hs, _⟩
  swap
  · rw [hsa, hsb] at hs
    exact absurd hs (lt_irrefl n)
  obtain ⟨v', hv'⟩ : ∃ v' : P, (v' : Finset E) = v := ⟨⟨v, hv⟩, rfl⟩
  rw [← hv'] at hav hg
  have hxv := Int.toNat_of_nonneg (hxd.1 v')
  have hyv := Int.toNat_of_nonneg (hyd.1 v')
  have hxy' : x v' < y v' := by
    have h1 := ha v'
    have h2 := hb v'
    omega
  have huv : (u : Finset E) ≠ (v' : Finset E) := by
    intro h
    rw [h] at hab
    omega
  have huv' : u ≠ v' := fun h => huv (congrArg Subtype.val h)
  have hxval : ∀ p : P, ((inc (dec a u) v' p : ℕ) : ℤ) =
      x p - IndicatorVec {u} p + IndicatorVec {v'} p := by
    intro p
    simp only [IndicatorVec]
    have hxp := Int.toNat_of_nonneg (hxd.1 p)
    have hap := ha p
    by_cases hpu : p = u
    · have hmu : p ∈ ({u} : Finset P) := Finset.mem_singleton.mpr hpu
      have hmv : p ∉ ({v'} : Finset P) :=
        fun h => huv' (hpu.symm.trans (Finset.mem_singleton.mp h))
      have h1 : inc (dec a u) v' p = a u - 1 := by
        rw [hpu, inc_ne _ _ _ huv, dec_self]
      rw [h1, if_pos hmu, if_neg hmv, hpu]
      have hau := ha u
      omega
    · by_cases hpv : p = v'
      · have hmu : p ∉ ({u} : Finset P) :=
          fun h => huv' ((Finset.mem_singleton.mp h).symm.trans hpv)
        have hmv : p ∈ ({v'} : Finset P) := Finset.mem_singleton.mpr hpv
        have h1 : inc (dec a u) v' p = a v' + 1 := by
          rw [hpv, inc_self, dec_ne _ _ _ (Ne.symm huv)]
        rw [h1, if_neg hmu, if_pos hmv, hpv]
        have hav' := ha v'
        omega
      · have hmu : p ∉ ({u} : Finset P) := fun h => hpu (Finset.mem_singleton.mp h)
        have hmv : p ∉ ({v'} : Finset P) := fun h => hpv (Finset.mem_singleton.mp h)
        have hpu' : (p : Finset E) ≠ (u : Finset E) := fun h => hpu (Subtype.ext h)
        have hpv' : (p : Finset E) ≠ (v' : Finset E) := fun h => hpv (Subtype.ext h)
        have h1 : inc (dec a u) v' p = a p := by
          rw [inc_ne _ _ _ hpv', dec_ne _ _ _ hpu']
        rw [h1, if_neg hmu, if_neg hmv]
        omega
  have hyval : ∀ p : P, ((inc (dec b v') u p : ℕ) : ℤ) =
      y p + IndicatorVec {u} p - IndicatorVec {v'} p := by
    intro p
    simp only [IndicatorVec]
    have hyp := Int.toNat_of_nonneg (hyd.1 p)
    have hbp := hb p
    by_cases hpu : p = u
    · have hmu : p ∈ ({u} : Finset P) := Finset.mem_singleton.mpr hpu
      have hmv : p ∉ ({v'} : Finset P) :=
        fun h => huv' (hpu.symm.trans (Finset.mem_singleton.mp h))
      have h1 : inc (dec b v') u p = b u + 1 := by
        rw [hpu, inc_self, dec_ne _ _ _ huv]
      rw [h1, if_pos hmu, if_neg hmv, hpu]
      have hbu := hb u
      omega
    · by_cases hpv : p = v'
      · have hmu : p ∉ ({u} : Finset P) :=
          fun h => huv' ((Finset.mem_singleton.mp h).symm.trans hpv)
        have hmv : p ∈ ({v'} : Finset P) := Finset.mem_singleton.mpr hpv
        have h1 : inc (dec b v') u p = b v' - 1 := by
          rw [hpv, inc_ne _ _ _ (Ne.symm huv), dec_self]
        rw [h1, if_neg hmu, if_pos hmv, hpv]
        have hbv := hb v'
        omega
      · have hmu : p ∉ ({u} : Finset P) := fun h => hpu (Finset.mem_singleton.mp h)
        have hmv : p ∉ ({v'} : Finset P) := fun h => hpv (Finset.mem_singleton.mp h)
        have hpu' : (p : Finset E) ≠ (u : Finset E) := fun h => hpu (Subtype.ext h)
        have hpv' : (p : Finset E) ≠ (v' : Finset E) := fun h => hpv (Subtype.ext h)
        have h1 : inc (dec b v') u p = b p := by
          rw [inc_ne _ _ _ hpu', dec_ne _ _ _ hpv']
        rw [h1, if_neg hmu, if_neg hmv]
        omega
  have hsx : ∑ p, (x p - IndicatorVec {u} p + IndicatorVec {v'} p) = (n : ℤ) := by
    rw [Finset.sum_congr rfl (fun p _ => (hxval p).symm), hcast, sum_inc P _ _ v'.2,
      sum_dec P a _ u.2 (by omega), hsa]
  have hsy : ∑ p, (y p + IndicatorVec {u} p - IndicatorVec {v'} p) = (n : ℤ) := by
    rw [Finset.sum_congr rfl (fun p _ => (hyval p).symm), hcast, sum_inc P _ _ u.2,
      sum_dec P b _ v'.2 (by omega), hsb]
  have hx0 : ∀ p, 0 ≤ x p - IndicatorVec {u} p + IndicatorVec {v'} p := by
    intro p
    rw [← hxval p]
    exact Int.natCast_nonneg _
  have hy0 : ∀ p, 0 ≤ y p + IndicatorVec {u} p - IndicatorVec {v'} p := by
    intro p
    rw [← hyval p]
    exact Int.natCast_nonneg _
  refine ⟨v', ?_, ?_⟩
  · unfold SuppNeg
    exact (memf _ _ v').mpr hxy'
  have e1 : (if (∀ p, 0 ≤ x p) ∧ ∑ p, x p = (n : ℤ) then
      ((loadPotential c (fun p => (x p).toNat) : ℝ) : WithTop ℝ) else ⊤) =
      ((Phi c P a : ℝ) : WithTop ℝ) := by
    rw [if_pos hxd, lp_eq c P _ a (fun p => ha p)]
  have e2 : (if (∀ p, 0 ≤ y p) ∧ ∑ p, y p = (n : ℤ) then
      ((loadPotential c (fun p => (y p).toNat) : ℝ) : WithTop ℝ) else ⊤) =
      ((Phi c P b : ℝ) : WithTop ℝ) := by
    rw [if_pos hyd, lp_eq c P _ b (fun p => hb p)]
  have e3 : (if (∀ p, 0 ≤ x p - IndicatorVec {u} p + IndicatorVec {v'} p) ∧
        ∑ p, (x p - IndicatorVec {u} p + IndicatorVec {v'} p) = (n : ℤ) then
      ((loadPotential c (fun p => (x p - IndicatorVec {u} p + IndicatorVec {v'} p).toNat) : ℝ) :
        WithTop ℝ) else ⊤) =
      ((Phi c P (inc (dec a u) v') : ℝ) : WithTop ℝ) := by
    rw [if_pos ⟨hx0, hsx⟩, lp_eq c P (fun p => (x p - IndicatorVec {u} p + IndicatorVec {v'} p).toNat)
      (inc (dec a u) v') (fun p => by
        show inc (dec a u) v' p = (x p - IndicatorVec {u} p + IndicatorVec {v'} p).toNat
        rw [← hxval p, Int.toNat_natCast])]
  have e4 : (if (∀ p, 0 ≤ y p + IndicatorVec {u} p - IndicatorVec {v'} p) ∧
        ∑ p, (y p + IndicatorVec {u} p - IndicatorVec {v'} p) = (n : ℤ) then
      ((loadPotential c (fun p => (y p + IndicatorVec {u} p - IndicatorVec {v'} p).toNat) : ℝ) :
        WithTop ℝ) else ⊤) =
      ((Phi c P (inc (dec b v') u) : ℝ) : WithTop ℝ) := by
    rw [if_pos ⟨hy0, hsy⟩, lp_eq c P (fun p => (y p + IndicatorVec {u} p - IndicatorVec {v'} p).toNat)
      (inc (dec b v') u) (fun p => by
        show inc (dec b v') u p = (y p + IndicatorVec {u} p - IndicatorVec {v'} p).toNat
        rw [← hyval p, Int.toNat_natCast])]
  show (if (∀ p, 0 ≤ x p) ∧ ∑ p, x p = (n : ℤ) then
      ((loadPotential c (fun p => (x p).toNat) : ℝ) : WithTop ℝ) else ⊤) +
    (if (∀ p, 0 ≤ y p) ∧ ∑ p, y p = (n : ℤ) then
      ((loadPotential c (fun p => (y p).toNat) : ℝ) : WithTop ℝ) else ⊤) ≥
    (if (∀ p, 0 ≤ x p - IndicatorVec {u} p + IndicatorVec {v'} p) ∧
        ∑ p, (x p - IndicatorVec {u} p + IndicatorVec {v'} p) = (n : ℤ) then
      ((loadPotential c (fun p => (x p - IndicatorVec {u} p + IndicatorVec {v'} p).toNat) : ℝ) :
        WithTop ℝ) else ⊤) +
    (if (∀ p, 0 ≤ y p + IndicatorVec {u} p - IndicatorVec {v'} p) ∧
        ∑ p, (y p + IndicatorVec {u} p - IndicatorVec {v'} p) = (n : ℤ) then
      ((loadPotential c (fun p => (y p + IndicatorVec {u} p - IndicatorVec {v'} p).toNat) : ℝ) :
        WithTop ℝ) else ⊤)
  rw [e1, e2, e3, e4, ge_iff_le, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  exact hg
