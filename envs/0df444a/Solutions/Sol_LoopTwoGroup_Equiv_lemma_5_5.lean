-- Prove2me | solution 1 for LoopTwoGroup.Equiv.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:18:16.26527+00:00
-- url     : https://prove2.me/submissions/e71dd480-fbdc-41a8-b4df-6099ef323508

import Definitions.Def_LoopTwoGroup_Equiv_Model
import Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_4

set_option autoImplicit false
open LoopTwoGroup.Equiv MeasureTheory InnerProductSpace

theorem solution {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] (L : InvLieBracket g) (k : ℝ) :
    ∃ (Φ : LInfHom (Pk L k) (gk L k)) (Λ : LInfHom (EOmega L) (Pk L k)),
      PhiComponents L k Φ ∧ LambdaComponents L k Λ ∧
      Function.Injective Λ.f0 ∧ Function.Injective Λ.f1 ∧
      LinearMap.range Λ.f0 = LinearMap.ker Φ.f0 ∧
      LinearMap.range Λ.f1 = LinearMap.ker Φ.f1 := by
  obtain ⟨Φ, hΦ⟩ := lemma_5_4 L k
  let j : loopSpace g →ₗ[ℝ] pathSpace g := {
    toFun := fun a => ⟨a.1, a.2.1⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let j1 : loopSpace g →ₗ[ℝ] (loopSpace g × ℝ) := {
    toFun := fun a => (a, 0)
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  let β (a b : loopSpace g) : ℝ := Φ.f2 (j a) (j b)
  have h0 (a : loopSpace g) : Φ.f0 (j a) = 0 := (hΦ.1 (j a)).trans a.2.2
  have h1 (h : loopSpace g × ℝ) : Φ.f1 h = h.2 := hΦ.2.1 h
  have hbr (a b : loopSpace g) :
      j (loopBracket L a b) = pathBracket L (j a) (j b) := rfl
  have hmixed (a b : loopSpace g) :
      pathLoopBracket L (j a) b = loopBracket L a b := rfl
  have hbeta (a b : loopSpace g) :
      β a b = 2 * k * ∫ t in (0 : ℝ)..(2 * Real.pi),
        ⟪b.1 t, dpath a.1 t⟫_ℝ := by
    have h := Φ.eq4 (j a) (b, 0)
    rw [h1] at h
    simpa [β, Pk, gk, j] using h
  have hcyc (a b c : loopSpace g) :
      β a (loopBracket L b c) + β b (loopBracket L c a) +
        β c (loopBracket L a b) = 0 := by
    have h := Φ.eq5 (j a) (j b) (j c)
    simpa [β, Pk, gk, h0, ← hbr] using h.symm
  have hcentral (p : pathSpace g) (r : ℝ) :
      (Pk L k).l2h p (0, r) = 0 := by
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change L.br (p.1 t) 0 = 0
      simp
    · simp [Pk]
  let Λ : LInfHom (EOmega L) (Pk L k) := {
    f0 := j
    f1 := j1
    f2 := fun a b => (0, -β a b)
    f2_add := by
      intro a b c
      apply Prod.ext <;> simp [β, Φ.f2_add]
      exact add_comm _ _
    f2_smul := by
      intro r a b
      apply Prod.ext <;> simp [β, Φ.f2_smul]
    f2_skew := by
      intro a b
      apply Prod.ext
      · simp
      · change -β a b = -(-β b a)
        exact congrArg Neg.neg (Φ.f2_skew (j a) (j b))
    chain := by intro a; rfl
    eq3 := by
      intro a b
      change (0 : pathSpace g) = j (loopBracket L a b) - pathBracket L (j a) (j b)
      rw [hbr, sub_self]
    eq4 := by
      intro a b
      apply Prod.ext
      · change (0 : loopSpace g) = loopBracket L a b - pathLoopBracket L (j a) b
        rw [hmixed, sub_self]
      · change -β a b = 0 - (2 * k * ∫ t in (0 : ℝ)..(2 * Real.pi),
          ⟪b.1 t, dpath a.1 t⟫_ℝ)
        rw [hbeta, zero_sub]
    eq5 := by
      intro a b c
      change j1 0 - (0 : loopSpace g × ℝ) =
        (0, -β a (loopBracket L b c)) + (0, -β b (loopBracket L c a)) +
          (0, -β c (loopBracket L a b)) +
          (Pk L k).l2h (j a) (0, -β b c) +
          (Pk L k).l2h (j b) (0, -β c a) +
          (Pk L k).l2h (j c) (0, -β a b)
      simp only [map_zero, sub_zero]
      rw [hcentral, hcentral, hcentral]
      simp only [add_zero]
      apply Prod.ext
      · simp
      · change (0 : ℝ) = -β a (loopBracket L b c) + -β b (loopBracket L c a) +
          -β c (loopBracket L a b)
        rw [← neg_add, ← neg_add, hcyc, neg_zero] }
  refine ⟨Φ, Λ, hΦ, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro a; rfl
    · intro a; rfl
    · intro a b
      apply Prod.ext
      · rfl
      · change -β a b = 2 * k * ∫ t in (0 : ℝ)..(2 * Real.pi),
          ⟪a.1 t, dpath b.1 t⟫_ℝ
        have hs : β a b = -β b a := Φ.f2_skew (j a) (j b)
        rw [hs, neg_neg]
        exact hbeta b a
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun p : pathSpace g => p.1) hab
  · intro a b hab
    exact congrArg Prod.fst hab
  · apply Submodule.ext
    intro p
    constructor
    · rintro ⟨a, rfl⟩
      exact h0 a
    · intro hp
      have hp' : p.1 (2 * Real.pi) = 0 := by
        rw [← hΦ.1 p]
        exact hp
      let a : loopSpace g := ⟨p.1, p.2, hp'⟩
      exact ⟨a, Subtype.ext rfl⟩
  · apply Submodule.ext
    intro p
    constructor
    · rintro ⟨a, rfl⟩
      exact h1 (a, 0)
    · intro hp
      have hp' : p.2 = 0 := by
        rw [← h1 p]
        exact hp
      refine ⟨p.1, ?_⟩
      apply Prod.ext
      · rfl
      · exact hp'.symm
