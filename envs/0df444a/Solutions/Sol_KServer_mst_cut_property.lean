-- Prove2me | solution 1 for KServer.mst_cut_property
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T10:48:48.366365+00:00
-- url     : https://prove2.me/submissions/fd95dec8-f8c7-4868-b56c-c11f06d493e0

import Mathlib


/-- Replacing the value of a function at one point of a finite sum. -/
private theorem sum_upd {V : Type} [DecidableEq V] (s : Finset V) (f g : V → ℝ) (p : V)
    (hp : p ∈ s) (h : ∀ v ∈ s, v ≠ p → f v = g v) :
    ∑ v ∈ s, f v = ∑ v ∈ s, g v + (f p - g p) := by
  rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ g hp,
    Finset.sum_congr rfl (fun v hv => h v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv))]
  ring

/-- **Re-rooting.** A rooted spanning structure is a parent map together with a rank
certificate; its edge multiset is `{v, par v}` for `v` other than the root. Any vertex can
be made the root without changing the total weight. -/
private theorem reroot {V : Type} [Fintype V] [DecidableEq V] (ω : V → V → ℝ)
    (hsymm : ∀ u v, ω u v = ω v u) :
    ∀ (m : ℕ) (ρ : V) (par : V → V) (rk : V → ℕ) (a : V),
      rk ρ = 0 → (∀ v, rk v = 0 → v = ρ) → (∀ v, v ≠ ρ → rk (par v) < rk v) →
      rk a ≤ m →
      ∃ (par' : V → V) (rk' : V → ℕ),
        rk' a = 0 ∧ (∀ v, rk' v = 0 → v = a) ∧ (∀ v, v ≠ a → rk' (par' v) < rk' v) ∧
        (∀ v, rk a < rk v → par' v = par v) ∧
        (∑ v ∈ Finset.univ.erase a, ω v (par' v))
          = ∑ v ∈ Finset.univ.erase ρ, ω v (par v) := by
  intro m
  induction m with
  | zero =>
      intro ρ par rk a hrk huniq hpar hle
      have ha : a = ρ := huniq a (Nat.le_zero.mp hle)
      subst ha
      exact ⟨par, rk, hrk, huniq, hpar, fun v _ => rfl, rfl⟩
  | succ m ih =>
      intro ρ par rk a hrk huniq hpar hle
      by_cases h0 : rk a = 0
      · have ha : a = ρ := huniq a h0
        subst ha
        exact ⟨par, rk, hrk, huniq, hpar, fun v _ => rfl, rfl⟩
      · have haρ : a ≠ ρ := fun h => h0 (by rw [h, hrk])
        set b : V := par a with hb
        have hba : rk b < rk a := hpar a haρ
        have hbm : rk b ≤ m := by omega
        obtain ⟨par₁, rk₁, h1a, h1u, h1p, h1e, h1s⟩ := ih ρ par rk b hrk huniq hpar hbm
        have hpar₁a : par₁ a = par a := h1e a hba
        have hab : a ≠ b := fun h => by rw [h] at hba; omega
        -- one-step re-rooting from `b` to its child `a`
        refine ⟨Function.update par₁ b a,
          fun v => if v = a then 0 else if v = b then 1 else rk₁ v + 1, ?_, ?_, ?_, ?_, ?_⟩
        · simp
        · intro v hv
          dsimp only at hv
          by_cases hva : v = a
          · exact hva
          · rw [if_neg hva] at hv
            by_cases hvb : v = b
            · rw [if_pos hvb] at hv; exact absurd hv one_ne_zero
            · rw [if_neg hvb] at hv; omega
        · intro v hva
          dsimp only
          rw [if_neg hva]
          by_cases hvb : v = b
          · subst hvb
            rw [Function.update_self, if_pos rfl]
            simp
          · rw [if_neg hvb, Function.update_of_ne hvb]
            have hlt : rk₁ (par₁ v) < rk₁ v := h1p v hvb
            have hv0 : rk₁ v ≠ 0 := fun h => hvb (h1u v h)
            by_cases hpa : par₁ v = a
            · rw [hpa, if_pos rfl]; omega
            · rw [if_neg hpa]
              by_cases hpb : par₁ v = b
              · rw [hpb, if_pos rfl]; omega
              · rw [if_neg hpb]; omega
        · intro v hv
          have hvb : v ≠ b := fun h => by rw [h] at hv; omega
          have hva : v ≠ a := fun h => by rw [h] at hv; omega
          rw [Function.update_of_ne hvb]
          exact h1e v (by omega)
        · have hbmem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
          have hamem : a ∈ Finset.univ.erase b := Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩
          rw [← Finset.add_sum_erase _ (fun v => ω v (Function.update par₁ b a v)) hbmem,
            ← h1s, ← Finset.add_sum_erase _ (fun v => ω v (par₁ v)) hamem]
          have hset : (Finset.univ.erase a).erase b = (Finset.univ.erase b).erase a := by
            ext x
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            tauto
          have hcongr : ∑ v ∈ (Finset.univ.erase a).erase b,
              ω v (Function.update par₁ b a v)
              = ∑ v ∈ (Finset.univ.erase b).erase a, ω v (par₁ v) := by
            rw [← hset]
            refine Finset.sum_congr rfl fun v hv => ?_
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
          rw [hcongr]
          have e1 : ω b (Function.update par₁ b a b) = ω a (par₁ a) := by
            rw [Function.update_self, hpar₁a, ← hb, hsymm]
          rw [e1]

/-- **The cut property.** If `ω r a` is a minimum-weight edge at `r`, then some rooted
spanning structure of no larger weight contains the edge `{r, a}`. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V] (ω : V → V → ℝ)
    (hsymm : ∀ u v, ω u v = ω v u) (r a : V) (hra : r ≠ a)
    (hmin : ∀ b, b ≠ r → ω r a ≤ ω r b)
    (ρ : V) (par : V → V) (rk : V → ℕ)
    (hrk : rk ρ = 0) (huniq : ∀ v, rk v = 0 → v = ρ)
    (hpar : ∀ v, v ≠ ρ → rk (par v) < rk v) :
    ∃ (par' : V → V) (rk' : V → ℕ),
      rk' a = 0 ∧ (∀ v, rk' v = 0 → v = a) ∧ (∀ v, v ≠ a → rk' (par' v) < rk' v) ∧
      par' r = a ∧
      (∑ v ∈ Finset.univ.erase a, ω v (par' v))
        ≤ ∑ v ∈ Finset.univ.erase ρ, ω v (par v) := by
  obtain ⟨par₂, rk₂, h2a, h2u, h2p, -, h2s⟩ :=
    reroot ω hsymm (rk a) ρ par rk a hrk huniq hpar le_rfl
  have hr0 : rk₂ r ≠ 0 := fun h => hra (h2u r h)
  have hlt : rk₂ (par₂ r) < rk₂ r := h2p r (fun h => hr0 (by rw [h, h2a]))
  have hne : par₂ r ≠ r := fun h => by rw [h] at hlt; omega
  refine ⟨Function.update par₂ r a, rk₂, h2a, h2u, ?_, Function.update_self _ _ _, ?_⟩
  · intro v hva
    by_cases hvr : v = r
    · subst hvr
      rw [Function.update_self, h2a]
      omega
    · rw [Function.update_of_ne hvr]; exact h2p v hva
  · have hrmem : r ∈ Finset.univ.erase a :=
      Finset.mem_erase.mpr ⟨hra, Finset.mem_univ r⟩
    have hsum := sum_upd (Finset.univ.erase a)
      (fun v => ω v (Function.update par₂ r a v)) (fun v => ω v (par₂ v)) r hrmem
      (fun v _ hv => by
        show ω v (Function.update par₂ r a v) = ω v (par₂ v)
        rw [Function.update_of_ne hv])
    rw [hsum, h2s]
    simp only [Function.update_self]
    have := hmin (par₂ r) hne
    rw [hsymm r a, hsymm r (par₂ r)] at this
    have h2 : ω a r ≤ ω (par₂ r) r := this
    rw [hsymm a r] at h2
    rw [hsymm (par₂ r) r] at h2
    linarith
