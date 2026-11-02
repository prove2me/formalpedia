-- Prove2me | solution 1 for LoopTwoGroup.Equiv.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:03:29.597192+00:00
-- url     : https://prove2.me/submissions/6c94eb54-0f85-4ace-ad2f-71967497c335

import Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_3
import Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_5
import Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_8

set_option autoImplicit false
open LoopTwoGroup.Equiv

private theorem phi_unique {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    (L : InvLieBracket g) (k : ℝ) {F G : LInfHom (Pk L k) (gk L k)}
    (hF : PhiComponents L k F) (hG : PhiComponents L k G) : F = G := by
  have h0 : F.f0 = G.f0 := LinearMap.ext fun p => (hF.1 p).trans (hG.1 p).symm
  have h1 : F.f1 = G.f1 := LinearMap.ext fun h => (hF.2.1 h).trans (hG.2.1 h).symm
  have h2 : F.f2 = G.f2 := funext fun p => funext fun q =>
    (hF.2.2 p q).trans (hG.2.2 p q).symm
  cases F; cases G; cases h0; cases h1; cases h2; rfl

private noncomputable def loopRealLieBracket {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    (L : InvLieBracket g) : RealLieBracket (loopSpace g) where
  br := {
    toFun := fun a => {
      toFun := loopBracket L a
      map_add' := by intros b c; ext t; simp [loopBracket, pathBracket]
      map_smul' := by intros r b; ext t; simp [loopBracket, pathBracket] }
    map_add' := by intros a b; ext c t; simp [loopBracket, pathBracket]
    map_smul' := by intros r a; ext b t; simp [loopBracket, pathBracket] }
  self := by intro a; ext t; exact L.self (a.1 t)
  jacobi := by intro a b c; ext t; exact L.jacobi (a.1 t) (b.1 t) (c.1 t)

theorem solution {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] (L : InvLieBracket g) (k : ℝ) :
    ∃ (Λ : LInfHom (EOmega L) (Pk L k)) (Φ : LInfHom (Pk L k) (gk L k)),
      Function.Injective Λ.f0 ∧ Function.Injective Λ.f1 ∧
      LinearMap.range Λ.f0 = LinearMap.ker Φ.f0 ∧
      LinearMap.range Λ.f1 = LinearMap.ker Φ.f1 ∧
      Function.Surjective Φ.f0 ∧ Function.Surjective Φ.f1 ∧
      (∀ a b, compF2 Λ Φ a b = 0) ∧
      Equivalent (EOmega L) trivialData ∧ IsEquivalence Φ := by
  obtain ⟨Φ, Λ, hΦ, _, hi0, hi1, hk0, hk1⟩ := lemma_5_5 L k
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => t / (2 * Real.pi)) (Set.Icc 0 (2 * Real.pi)) := by
    exact contDiffOn_id.div_const (2 * Real.pi)
  have hf0 : (0 : ℝ) / (2 * Real.pi) = 0 := zero_div _
  have hf1 : (2 * Real.pi) / (2 * Real.pi) = (1 : ℝ) :=
    div_self (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  obtain ⟨Φ', Ψ, hΦ', _, hc0, hc1, hc2, T, _⟩ :=
    lemma_5_8 L k (fun t => t / (2 * Real.pi)) hf hf0 hf1
  have heq : Φ' = Φ := phi_unique L k hΦ' hΦ
  subst Φ'
  have hz1 (b : loopSpace g) : Φ.f1 (Λ.f1 b) = 0 := by
    have h : Λ.f1 b ∈ LinearMap.range Λ.f1 := ⟨b, rfl⟩
    rw [hk1] at h
    exact h
  refine ⟨Λ, Φ, hi0, hi1, hk0, hk1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨Ψ.f0 a, congrArg (fun f => f a) hc0⟩
  · intro a
    exact ⟨Ψ.f1 a, congrArg (fun f => f a) hc1⟩
  · intro a b
    have hφ := Φ.eq4 (Λ.f0 a) (Λ.f1 b)
    rw [Λ.chain] at hφ
    change Φ.f2 (Λ.f0 a) (Λ.f0 b) = _ at hφ
    simp only [gk, sub_zero] at hφ
    have hLambda := congrArg (fun z => Φ.f1 z) (Λ.eq4 a b)
    change Φ.f1 (Λ.f2 a b) =
      Φ.f1 (Λ.f1 (loopBracket L a b) - (Pk L k).l2h (Λ.f0 a) (Λ.f1 b)) at hLambda
    rw [map_sub, hz1] at hLambda
    simp only [compF2, hφ, hLambda, zero_sub, add_neg_cancel]
  · exact lemma_5_3 (loopRealLieBracket L)
  · refine ⟨Ψ, ⟨T⟩, ⟨{ τ := 0, hom0 := ?_, hom1 := ?_, eq7 := ?_ }⟩⟩
    · intro a; rw [hc0]; simp [gk]
    · intro a; rw [hc1]; simp [gk]
    · intro a b; rw [hc2]; simp [gk]
