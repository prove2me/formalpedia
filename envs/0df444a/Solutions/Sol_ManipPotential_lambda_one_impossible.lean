-- Prove2me | solution 1 for ManipPotential.lambda_one_impossible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T19:52:35.334047+00:00
-- url     : https://prove2.me/submissions/b284ca6c-1c8c-4cb4-a6a0-d7290a25a872

import Mathlib
import Definitions.Def_ManipPotential_GAxioms

open ManipPotential

namespace LambdaOneAux

def mkP (f g : Fin 3 → Fin 3) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Equiv.Perm (Fin 3) := ⟨f, g, h1, h2⟩

def p0 : Equiv.Perm (Fin 3) := mkP ![0, 1, 2] ![0, 1, 2] (by decide) (by decide)

def p1 : Equiv.Perm (Fin 3) := mkP ![0, 2, 1] ![0, 2, 1] (by decide) (by decide)

def p2 : Equiv.Perm (Fin 3) := mkP ![1, 0, 2] ![1, 0, 2] (by decide) (by decide)

def p3 : Equiv.Perm (Fin 3) := mkP ![2, 0, 1] ![1, 2, 0] (by decide) (by decide)

def p4 : Equiv.Perm (Fin 3) := mkP ![1, 2, 0] ![2, 0, 1] (by decide) (by decide)

def p5 : Equiv.Perm (Fin 3) := mkP ![2, 1, 0] ![2, 1, 0] (by decide) (by decide)


theorem core (φ : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → Fin 3)
    (hSP : ∀ σ τ σ' : Equiv.Perm (Fin 3), σ (φ σ τ) ≤ σ (φ σ' τ))
    (hA : ∀ σ τ : Equiv.Perm (Fin 3), φ σ τ = φ τ σ)
    (hU : ∀ σ : Equiv.Perm (Fin 3), φ σ σ = σ.symm 0) : False := by
  obtain ⟨u02, hu02⟩ : ∃ u, φ p0 p2 = u := ⟨_, rfl⟩
  have hu20 : φ p2 p0 = u02 := (hA _ _).trans hu02
  obtain ⟨u03, hu03⟩ : ∃ u, φ p0 p3 = u := ⟨_, rfl⟩
  have hu30 : φ p3 p0 = u03 := (hA _ _).trans hu03
  obtain ⟨u04, hu04⟩ : ∃ u, φ p0 p4 = u := ⟨_, rfl⟩
  have hu40 : φ p4 p0 = u04 := (hA _ _).trans hu04
  obtain ⟨u05, hu05⟩ : ∃ u, φ p0 p5 = u := ⟨_, rfl⟩
  have hu50 : φ p5 p0 = u05 := (hA _ _).trans hu05
  obtain ⟨u12, hu12⟩ : ∃ u, φ p1 p2 = u := ⟨_, rfl⟩
  have hu21 : φ p2 p1 = u12 := (hA _ _).trans hu12
  obtain ⟨u13, hu13⟩ : ∃ u, φ p1 p3 = u := ⟨_, rfl⟩
  have hu31 : φ p3 p1 = u13 := (hA _ _).trans hu13
  obtain ⟨u14, hu14⟩ : ∃ u, φ p1 p4 = u := ⟨_, rfl⟩
  have hu41 : φ p4 p1 = u14 := (hA _ _).trans hu14
  obtain ⟨u15, hu15⟩ : ∃ u, φ p1 p5 = u := ⟨_, rfl⟩
  have hu51 : φ p5 p1 = u15 := (hA _ _).trans hu15
  obtain ⟨u25, hu25⟩ : ∃ u, φ p2 p5 = u := ⟨_, rfl⟩
  have hu52 : φ p5 p2 = u25 := (hA _ _).trans hu25
  obtain ⟨u34, hu34⟩ : ∃ u, φ p3 p4 = u := ⟨_, rfl⟩
  have hu43 : φ p4 p3 = u34 := (hA _ _).trans hu34
  obtain ⟨u35, hu35⟩ : ∃ u, φ p3 p5 = u := ⟨_, rfl⟩
  have hu53 : φ p5 p3 = u35 := (hA _ _).trans hu35
  have c0 := hSP p2 p0 p3
  rw [hu20, hu30] at c0
  have c1 := hSP p3 p5 p2
  rw [hu35, hu25] at c1
  have c2 := hSP p1 p4 p0
  rw [hu14, hu04] at c2
  have c3 := hSP p5 p3 p4
  rw [hu53, hu43] at c3
  have c4 := hSP p0 p4 p3
  rw [hu04, hu34] at c4
  have c5 := hSP p0 p2 p1
  rw [hu02, hu12] at c5
  have c6 := hSP p1 p3 p5
  rw [hu13, hu53] at c6
  have c7 := hSP p1 p5 p5
  rw [hu15, hU p5] at c7
  have c8 := hSP p4 p3 p0
  rw [hu43, hu03] at c8
  have c9 := hSP p4 p1 p5
  rw [hu41, hu51] at c9
  have c10 := hSP p2 p5 p0
  rw [hu25, hu05] at c10
  have c11 := hSP p5 p2 p2
  rw [hu52, hU p2] at c11
  have c12 := hSP p5 p1 p2
  rw [hu51, hu21] at c12
  have c13 := hSP p4 p0 p0
  rw [hu40, hU p0] at c13
  have c14 := hSP p3 p4 p4
  rw [hu34, hU p4] at c14
  have c15 := hSP p0 p3 p3
  rw [hu03, hU p3] at c15
  have c16 := hSP p3 p1 p2
  rw [hu31, hu21] at c16
  have c17 := hSP p3 p0 p5
  rw [hu30, hu50] at c17
  have c18 := hSP p2 p1 p1
  rw [hu21, hU p1] at c18
  clear hSP hA hU hu02 hu20 hu03 hu30 hu04 hu40 hu05 hu50 hu12 hu21 hu13 hu31 hu14 hu41 hu15 hu51 hu25 hu52 hu34 hu43 hu35 hu53
  fin_cases u34
  · exact absurd c14 (by decide)
  · fin_cases u25
    · exact absurd c11 (by decide)
    · fin_cases u03
      · exact absurd c8 (by decide)
      · fin_cases u35
        · exact absurd c1 (by decide)
        · fin_cases u02
          · exact absurd c0 (by decide)
          · fin_cases u05
            · fin_cases u12
              · exact absurd c5 (by decide)
              · fin_cases u15
                · exact absurd c12 (by decide)
                · exact absurd c7 (by decide)
                · fin_cases u13
                  · exact absurd c16 (by decide)
                  · fin_cases u04
                    · fin_cases u14
                      · exact absurd c9 (by decide)
                      · exact absurd c2 (by decide)
                      · exact absurd c2 (by decide)
                    · exact absurd c13 (by decide)
                    · exact absurd c4 (by decide)
                  · exact absurd c16 (by decide)
              · exact absurd c18 (by decide)
            · fin_cases u12
              · exact absurd c5 (by decide)
              · fin_cases u15
                · exact absurd c12 (by decide)
                · exact absurd c7 (by decide)
                · fin_cases u13
                  · exact absurd c16 (by decide)
                  · fin_cases u04
                    · fin_cases u14
                      · exact absurd c9 (by decide)
                      · exact absurd c2 (by decide)
                      · exact absurd c2 (by decide)
                    · exact absurd c13 (by decide)
                    · exact absurd c4 (by decide)
                  · exact absurd c16 (by decide)
              · exact absurd c18 (by decide)
            · fin_cases u12
              · exact absurd c5 (by decide)
              · fin_cases u15
                · exact absurd c12 (by decide)
                · exact absurd c7 (by decide)
                · fin_cases u13
                  · exact absurd c16 (by decide)
                  · fin_cases u04
                    · fin_cases u14
                      · exact absurd c9 (by decide)
                      · exact absurd c2 (by decide)
                      · exact absurd c2 (by decide)
                    · exact absurd c13 (by decide)
                    · exact absurd c4 (by decide)
                  · exact absurd c16 (by decide)
              · exact absurd c18 (by decide)
          · exact absurd c0 (by decide)
        · exact absurd c1 (by decide)
      · exact absurd c8 (by decide)
    · fin_cases u03
      · exact absurd c8 (by decide)
      · fin_cases u35
        · exact absurd c1 (by decide)
        · fin_cases u02
          · exact absurd c0 (by decide)
          · fin_cases u05
            · exact absurd c10 (by decide)
            · exact absurd c10 (by decide)
            · fin_cases u12
              · exact absurd c5 (by decide)
              · fin_cases u15
                · exact absurd c12 (by decide)
                · exact absurd c7 (by decide)
                · fin_cases u13
                  · exact absurd c16 (by decide)
                  · fin_cases u04
                    · fin_cases u14
                      · exact absurd c9 (by decide)
                      · exact absurd c2 (by decide)
                      · exact absurd c2 (by decide)
                    · exact absurd c13 (by decide)
                    · exact absurd c4 (by decide)
                  · exact absurd c16 (by decide)
              · exact absurd c18 (by decide)
          · exact absurd c0 (by decide)
        · fin_cases u02
          · exact absurd c0 (by decide)
          · fin_cases u05
            · exact absurd c10 (by decide)
            · exact absurd c10 (by decide)
            · fin_cases u12
              · exact absurd c5 (by decide)
              · fin_cases u15
                · exact absurd c12 (by decide)
                · exact absurd c7 (by decide)
                · fin_cases u13
                  · exact absurd c16 (by decide)
                  · exact absurd c6 (by decide)
                  · exact absurd c16 (by decide)
              · exact absurd c18 (by decide)
          · exact absurd c0 (by decide)
      · exact absurd c8 (by decide)
  · fin_cases u25
    · exact absurd c11 (by decide)
    · fin_cases u03
      · fin_cases u35
        · exact absurd c1 (by decide)
        · exact absurd c3 (by decide)
        · exact absurd c1 (by decide)
      · fin_cases u35
        · exact absurd c1 (by decide)
        · exact absurd c3 (by decide)
        · exact absurd c1 (by decide)
      · exact absurd c15 (by decide)
    · fin_cases u03
      · fin_cases u35
        · exact absurd c1 (by decide)
        · exact absurd c3 (by decide)
        · fin_cases u02
          · fin_cases u05
            · exact absurd c10 (by decide)
            · exact absurd c10 (by decide)
            · exact absurd c17 (by decide)
          · fin_cases u05
            · exact absurd c10 (by decide)
            · exact absurd c10 (by decide)
            · exact absurd c17 (by decide)
          · exact absurd c0 (by decide)
      · fin_cases u35
        · exact absurd c1 (by decide)
        · exact absurd c3 (by decide)
        · fin_cases u02
          · exact absurd c0 (by decide)
          · fin_cases u05
            · exact absurd c10 (by decide)
            · exact absurd c10 (by decide)
            · fin_cases u12
              · exact absurd c5 (by decide)
              · fin_cases u15
                · exact absurd c12 (by decide)
                · exact absurd c7 (by decide)
                · fin_cases u13
                  · exact absurd c16 (by decide)
                  · exact absurd c6 (by decide)
                  · exact absurd c16 (by decide)
              · exact absurd c18 (by decide)
          · exact absurd c0 (by decide)
      · exact absurd c15 (by decide)

end LambdaOneAux

namespace LambdaOneAux

/-- `Fin 3` as the first three candidates of `Fin (n+3)`. -/
def e3 (n : ℕ) : Fin 3 ≃ {x : Fin (n + 3) // (x : ℕ) < 3} where
  toFun u := ⟨⟨u.val, by omega⟩, u.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv u := by ext; rfl
  right_inv x := by ext; rfl

def ι (n : ℕ) (u : Fin 3) : Fin (n + 3) := ((e3 n u : {x : Fin (n + 3) // (x : ℕ) < 3}) : Fin (n + 3))

lemma ι_val (n : ℕ) (u : Fin 3) : ((ι n u : Fin (n + 3)) : ℕ) = u.val := rfl

/-- The ranking of `Fin (n+3)` that orders the first three candidates by `σ` and keeps the
others, in their natural order, below them. -/
def ρ (n : ℕ) (σ : Equiv.Perm (Fin 3)) : Ranking (n + 3) := σ.extendDomain (e3 n)

lemma ρ_ι (n : ℕ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3) : ρ n σ (ι n u) = ι n (σ u) := by
  unfold ρ ι
  exact Equiv.Perm.extendDomain_apply_image σ (e3 n) u

lemma ρ_fix (n : ℕ) (σ : Equiv.Perm (Fin 3)) (c : Fin (n + 3)) (hc : 3 ≤ (c : ℕ)) :
    ρ n σ c = c := by
  unfold ρ
  exact Equiv.Perm.extendDomain_apply_not_subtype σ (e3 n) (by omega)

lemma unitVec_nonneg {m : ℕ} (r : Ranking m) : (0 : Ranking m → ℚ) ≤ unitVec r := by
  intro x
  simp only [unitVec, Pi.zero_apply, Pi.single_apply]
  split_ifs <;> norm_num

end LambdaOneAux

open LambdaOneAux in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    ¬ ∃ g : (Ranking m → ℚ) → Fin m, GAxioms 0 g := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  rintro ⟨g, hF, hB, -⟩
  let F : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → Fin (n + 3) :=
    fun σ τ => g (unitVec (ρ n τ) + unitVec (ρ n σ))
  have hSP : ∀ σ τ σ', Ranking.WeaklyPrefers (ρ n σ) (F σ τ) (F σ' τ) := by
    intro σ τ σ'
    unfold BoundedMP at hB
    have := hB (unitVec (ρ n τ)) (unitVec_nonneg _) (ρ n σ) (ρ n σ') (1 : ℚ) (1 : ℚ)
      (by norm_num) (by norm_num) (by norm_num)
    simpa only [one_smul] using this
  have hA : ∀ σ τ, F σ τ = F τ σ := fun σ τ => by simp only [F, add_comm]
  have hι0 : ι n 0 = (0 : Fin (n + 3)) := Fin.ext (by simp [ι_val])
  have hU : ∀ σ, F σ σ = ι n (σ.symm 0) := by
    intro σ
    have h2 : (unitVec (ρ n σ) : Ranking (n + 3) → ℚ) + unitVec (ρ n σ) =
        (2 : ℚ) • unitVec (ρ n σ) := by
      rw [two_smul]
    unfold Faithful at hF
    have := hF (ρ n σ) 2 (by norm_num)
    simp only [F, h2, this, Ranking.top]
    rw [Equiv.symm_apply_eq, ρ_ι, Equiv.apply_symm_apply, hι0]
  have hR : ∀ σ τ, ((F σ τ : Fin (n + 3)) : ℕ) < 3 := by
    intro σ τ
    by_contra h
    push Not at h
    have h1 := hSP σ τ τ
    unfold Ranking.WeaklyPrefers at h1
    rw [hU τ, ρ_ι, ρ_fix n σ (F σ τ) h] at h1
    have h2 := Fin.le_def.mp h1
    rw [ι_val] at h2
    have := (σ (τ.symm 0)).isLt
    omega
  let φ : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → Fin 3 := fun σ τ => ⟨(F σ τ : ℕ), hR σ τ⟩
  have hFφ : ∀ σ τ, F σ τ = ι n (φ σ τ) := fun σ τ => Fin.ext (by simp [ι_val, φ])
  apply core φ
  · intro σ τ σ'
    have h1 := hSP σ τ σ'
    unfold Ranking.WeaklyPrefers at h1
    rw [hFφ, hFφ, ρ_ι, ρ_ι] at h1
    have h2 := Fin.le_def.mp h1
    rw [ι_val, ι_val] at h2
    exact Fin.le_def.mpr h2
  · intro σ τ
    exact Fin.ext (by simp only [φ]; rw [hA])
  · intro σ
    apply Fin.ext
    simp only [φ]
    rw [hU, ι_val]
