-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isComm_of_isFormalCoordinates_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4e1317e9-9a01-53f6-ba0f-ff29725b4194

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isComm_of_isFormalCoordinates_of_isCommutative

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem E6Aux_exists_pow_succ_eq_bot {C : Type} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J) :
    ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨m, hm⟩ := hJ
  exact ⟨m, by rw [pow_succ, hm]; exact zero_mul _⟩

theorem E6Aux_nilEval_comp {σ : Type} [Fintype σ] [DecidableEq σ] {B C C' : Type} [CommRing B] [CommRing C] [CommRing C']
    [Algebra B C] [Algebra B C'] (φ : C →ₐ[B] C') (n : ℕ) (ψ : MvPowerSeries σ B) (s : σ → C) :
    MvFormalGroup.nilEval n ψ (φ ∘ s) = φ (MvFormalGroup.nilEval n ψ s) := by
  unfold MvFormalGroup.nilEval
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hL : L.IsCommutative) {g : ℕ} (F : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ) : F.IsComm := by
  classical
  obtain ⟨-, hnil⟩ := hθ
  constructor
  intro i

  have hsw0 : ∀ k, MvPowerSeries.constantCoeff ((Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) B)) fun j => MvPowerSeries.X (Sum.inl j)) k) = 0 := by
    rintro (k | k) <;> exact MvPowerSeries.constantCoeff_X _

  have hu := MvPowerSeries.existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent (R := B) (σ := Fin g ⊕ Fin g)
    (fun C _ _ J z => MvFormalGroup.adicEval J z (F.toPowerSeries i))
    (by
      intro C C' _ _ _ _ J J' hJ hJ' φ hφ z hz
      obtain ⟨n, hn⟩ := E6Aux_exists_pow_succ_eq_bot J hJ
      obtain ⟨m, hm⟩ := E6Aux_exists_pow_succ_eq_bot J' hJ'
      have hn' : J ^ (n + m + 1) = ⊥ := le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
      have hm' : J' ^ (n + m + 1) = ⊥ := le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hm.le)
      show MvFormalGroup.adicEval J' (fun k => φ (z k)) (F.toPowerSeries i) = φ (MvFormalGroup.adicEval J z (F.toPowerSeries i))
      rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J' (n + m) hm' _ (fun k => φ (z k)) (fun k => hφ _ (hz k)),
        ← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J (n + m) hn' _ _ hz]
      exact E6Aux_nilEval_comp φ (n + m) (F.toPowerSeries i) z)
  refine hu.unique ?_ (fun C _ _ J hJ z hz => rfl)

  intro C _ _ J hJ z hz
  obtain ⟨n, hn⟩ := E6Aux_exists_pow_succ_eq_bot J hJ
  show MvFormalGroup.adicEval J z (F.toPowerSeries i) = MvFormalGroup.adicEval J z (MvPowerSeries.subst (Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) B)) fun j => MvPowerSeries.X (Sum.inl j)) (F.toPowerSeries i))
  rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hz,
    ← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hz,
    (MvFormalGroup.nilEval_subst_of_mem J n hn z hz (Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) B)) fun j => MvPowerSeries.X (Sum.inl j)) hsw0 (F.toPowerSeries i)).2]
  have hswap : (fun k => MvFormalGroup.nilEval n ((Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) B)) fun j => MvPowerSeries.X (Sum.inl j)) k) z) = Sum.elim (z ∘ Sum.inr) (z ∘ Sum.inl) := by
    funext k
    rcases k with k | k
    · exact MvFormalGroup.nilEval_X_of_mem J n hn z hz (Sum.inr k)
    · exact MvFormalGroup.nilEval_X_of_mem J n hn z hz (Sum.inl k)
  rw [hswap]
  have hz' : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by
    funext k; rcases k with k | k <;> rfl
  conv_lhs => rw [hz']

  obtain ⟨-, hinj, -, hhom⟩ := hnil C J n hn
  have hx : ∀ j, (z ∘ Sum.inl) j ∈ J := fun j => hz _
  have hy : ∀ j, (z ∘ Sum.inr) j ∈ J := fun j => hz _
  have hm1 : ∀ j, F.nilMul n (z ∘ Sum.inl) (z ∘ Sum.inr) j ∈ J := fun j =>
    (MvFormalGroup.nilEval_subst_of_mem J n hn _ (by rintro (k | k); exacts [hx k, hy k])
      F.toPowerSeries F.constantCoeff_eq_zero 0).1 j
  have hm2 : ∀ j, F.nilMul n (z ∘ Sum.inr) (z ∘ Sum.inl) j ∈ J := fun j =>
    (MvFormalGroup.nilEval_subst_of_mem J n hn _ (by rintro (k | k); exacts [hy k, hx k])
      F.toPowerSeries F.constantCoeff_eq_zero 0).1 j
  have key : F.nilMul n (z ∘ Sum.inl) (z ∘ Sum.inr) = F.nilMul n (z ∘ Sum.inr) (z ∘ Sum.inl) :=
    hinj _ _ hm1 hm2 (by rw [hhom _ _ hx hy, hhom _ _ hy hx]; exact hL.mul_comm _ _ _)
  exact congrFun key i

end S_GoodReductionJacobian_RelativeGroupLaw_isComm_of_isFormalCoordinates_of_isCommutative
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isComm_of_isFormalCoordinates_of_isCommutative (solution)
