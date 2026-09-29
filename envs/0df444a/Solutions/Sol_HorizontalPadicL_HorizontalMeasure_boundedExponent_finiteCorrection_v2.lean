-- Prove2me | solution 1 for HorizontalPadicL.HorizontalMeasure.boundedExponent_finiteCorrection_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:14:40.109032+00:00
-- url     : https://prove2.me/submissions/92b4aa33-8012-4f37-a0a2-da5ae256ff46

import Theorems.Thm_HorizontalPadicL_HorizontalMeasure_truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

theorem solution
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e)
    (hintegral : ∀ x : R, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p])
    (m : ℕ) (hm : 0 < m) (he : ∀ n, m ≤ e n)
    (htriv : μ.eval (trivialHorizontalCharacterV2 p e) ≠ 0) :
    ∃ A : Finset ℕ, μ.HasFiniteCorrection m A := by
  classical
  have hempty : (μ.truncatedFiniteLevel m he ∅ 1 : ℂ_[p]) =
      μ.eval (trivialHorizontalCharacterV2 p e) := by
    have htrivial : μ.eval (trivialHorizontalCharacterV2 p e) =
        (μ.finiteLevel ∅ 1 : ℂ_[p]) := by
      change (μ.finiteLevel ∅).sum (fun _ a ↦ (a : ℂ_[p]) * 1) = _
      simp only [mul_one]
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      congr 2
      exact Subsingleton.elim _ _
    rw [htrivial]
    congr 1
    unfold HorizontalMeasure.truncatedFiniteLevel
    have h : truncateHorizontalCoordinates (p := p) m he ∅ 1 = 1 :=
      Subsingleton.elim _ _
    rw [← h, Finsupp.mapDomain_apply (fun a b _ ↦ Subsingleton.elim a b)]
  let S : Set ℝ := {b | ∃ (A : Finset ℕ)
    (x : HorizontalFiniteGroup p (fun _ ↦ m) A),
    ‖(μ.truncatedFiniteLevel m he A x : ℂ_[p])‖ = b}
  have hS : S.Nonempty := ⟨_, ∅, 1, rfl⟩
  have hbounded : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro b ⟨A, x, rfl⟩
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).mpr (hintegral _)
  have hC : 0 < sSup S := by
    apply lt_of_lt_of_le _ (le_csSup hbounded (show _ ∈ S from ⟨∅, 1, rfl⟩))
    exact norm_pos_iff.mpr (hempty ▸ htriv)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨b, ⟨A, x, rfl⟩, hx⟩ :=
    exists_lt_of_lt_csSup hS (div_lt_self hC hp)
  refine ⟨A, ?_⟩
  intro χ horder hdisjoint
  by_contra hbad
  have hvanish : ∀ a : ℕ, a < p ^ m → Nat.Coprime a p →
      ∀ ξ : HorizontalCharacter p e, ξ.support ⊆ A →
        orderOf ξ.toMonoidHom ∣ p ^ m →
        μ.eval ((χ.powerOnSupport a).mulOnUnion ξ) = 0 := by
    intro a ha hcop ξ hsupport hξ
    by_contra hne
    exact hbad ⟨a, ha, hcop, ξ, hsupport, hξ, hne⟩
  have hle := μ.truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2
    m hm he A χ horder hdisjoint (sSup S) hC.le
    (fun y ↦ le_csSup hbounded ⟨A ∪ χ.support, y, rfl⟩) hvanish x
  exact (not_lt_of_ge hle) hx
