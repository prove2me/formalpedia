-- Prove2me | solution 1 for MasulloGRH.expDecayStage_transition
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:53:53.856938+00:00
-- url     : https://prove2.me/submissions/e57744d0-f233-4e2a-a4d9-faadd791cf6a

import Theorems.Thm_MasulloGRH_schwartzBruhat_pullback_quotient
import Theorems.Thm_MasulloGRH_expDecayStage_weighted_mem
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le

set_option autoImplicit false

universe u

namespace MasulloGRHTransAux

open MasulloGRH

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- the kernel of a module as a subgroup -/
def modKer {m : G → ℝ} (hm : IsModule m) : Subgroup G where
  carrier := {g | m g = 1}
  one_mem' := by
    show m 1 = 1
    have h := hm.map_mul 1 1
    rw [mul_one] at h
    have hp := hm.pos 1
    nlinarith
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    have h := hm.map_mul a a⁻¹
    rw [mul_inv_cancel, show m a = 1 from ha, one_mul] at h
    have h1 := hm.map_mul 1 1
    rw [mul_one] at h1
    have hp := hm.pos 1
    have : m 1 = 1 := by nlinarith
    rw [← h, this]

end MasulloGRHTransAux

open MasulloGRH MasulloGRHTransAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (hle : k' ≤ k) :
    ∃ f : ExpDecayStage G m I k → ExpDecayStage G m I k', Continuous f ∧
      ∀ y, ExpDecayStage.incl G m I k' (f y) = ExpDecayStage.incl G m I k y := by
  obtain ⟨P, hP⟩ := schwartzBruhat_pullback_quotient G k k' hk hk' hle
  have hm1 : ∀ (c : Subgroup G), IsGoodSubgroup c → ∀ h ∈ c, m h = 1 := by
    intro c hc h hh
    exact (isCompact_moduleKernel_and_compact_le G m hm (modKer hm.1) (fun g => Iff.rfl)).2
      c (isCompact_of_isGoodSubgroup G c hc) hh
  have hwf : ∀ (c : Subgroup G) (hc : IsGoodSubgroup c) (y : ExpDecayStage G m I c) (a : ℝ)
      (ha : a ∈ I), (ExpDecaySchwartz.weighted c a y.1).toFun =
        fun x : G ⧸ c => ((m x.out ^ a : ℝ) : ℂ) * y.1.toFun x.out := by
    intro c hc y a ha
    have hmem := expDecayStage_weighted_mem G m hm I hI hne c hc y a ha
    unfold ExpDecaySchwartz.weighted
    first
      | (erw [dif_pos hmem]; rfl)
      | (simp only [hmem, dif_pos]; rfl)
      | (split <;> [rfl; exact absurd hmem ‹_›])
  let f : ExpDecayStage G m I k → ExpDecayStage G m I k' := fun y =>
    ⟨y.1, fun h hh g => y.2 h (hle hh) g⟩
  refine ⟨f, ?_, fun y => rfl⟩
  refine continuous_iInf_rng.2 fun a => continuous_iInf_rng.2 fun ha => continuous_induced_rng.2 ?_
  have hcont : Continuous (fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a y.1) :=
    continuous_iff_le_induced.2 (iInf₂_le a ha)
  have heq : (fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k' a (f y).1) =
      fun y => P (ExpDecaySchwartz.weighted k a y.1) := by
    funext y
    apply Subtype.ext
    show (ExpDecaySchwartz.weighted k' a (f y).1).toFun =
      (P (ExpDecaySchwartz.weighted k a y.1)).toFun
    rw [hwf k' hk' (f y) a ha]
    funext x
    rw [hP, hwf k hk y a ha]
    beta_reduce
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hmap : QuotientGroup.map k' k (MonoidHom.id G) hle (QuotientGroup.mk g) =
          (QuotientGroup.mk g : G ⧸ k) := rfl
      rw [hmap]
      obtain ⟨h₁, hh₁⟩ := QuotientGroup.mk_out_eq_mul k' g
      obtain ⟨h₂, hh₂⟩ := QuotientGroup.mk_out_eq_mul k g
      rw [hh₁, hh₂]
      have e₁ : (f y).1.toFun (g * h₁) = y.1.toFun g := y.2 h₁ (hle h₁.2) g
      have e₂ : y.1.toFun (g * h₂) = y.1.toFun g := y.2 h₂ h₂.2 g
      rw [e₁, e₂, hm.1.map_mul, hm.1.map_mul, hm1 k' hk' h₁ h₁.2, hm1 k hk h₂ h₂.2]
  exact (P.continuous.comp hcont).congr fun y => (congrFun heq y).symm
