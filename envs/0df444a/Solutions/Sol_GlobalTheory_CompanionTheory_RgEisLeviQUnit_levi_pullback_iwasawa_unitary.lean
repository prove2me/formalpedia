-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.levi_pullback_iwasawa_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:29:58.17986+00:00
-- url     : https://prove2.me/submissions/efd3975c-dc08-42b2-9b69-aa833814ab25

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi_j
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi_K
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j_K
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi___44780f1c40f3
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j___a51c829f7f74
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pull_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_split
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi_cont
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_j_cont
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_uH_pk
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisLeviQUnit_c__par_21c7392b8182
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_j

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {_fF : Fintype ↥sᶜ} {_fD : DecidableEq ↥sᶜ}
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (hA : A.Good)
    (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) :
    ∃ (π : A.uQ ε s →* A.U ε ↥sᶜ) (j : A.U ε ↥sᶜ →* A.uQ ε s) (c : A.U ε ι → ℂ),
      IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uΓ ε _) (A.uK ε _) π j c ∧
      IsPull (A.uQ ε s) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε Set.univ) π c (A.uC ε ι) (A.uC ε _) ∧
      Iwa (A.uQ ε (Set.univ : Set ↥sᶜ)) (A.uK ε _) ∧
      PullHt (A.uK ε ι) (A.uQ ε s) π (fun g => A.uH ε Set.univ g - A.uH ε s g) (A.uH ε Set.univ) := by
  have hL := hA.toGoodL
  have hσ := hA.σσ
  obtain ⟨-, -, -, t1, -, -, hK⟩ := hT E R A hA ι ε
  obtain ⟨-, -, -, t2, -, -, hK'⟩ := hT E R A hA ↥sᶜ ε
  haveI := t1
  haveI := t2
  have hIs : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, h⟩ := hI g
    exact ⟨p, hp.1, k, hk, h⟩
  have hIu : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, h⟩ := hI g
    exact ⟨p, hp.2, k, hk, h⟩

  have hdec : ∀ q : A.uQ ε s, ∃ (P K₁ : A.uQ ε s), q = P * K₁ ∧ (P : A.U ε ι) ∈ A.uQ ε Set.univ ∧
      (K₁ : A.U ε ι) ∈ A.uK ε ι := fun q => by
    obtain ⟨p, hp, k, hk, h⟩ := hI q.1
    have hk' : k ∈ A.uQ ε s := by
      have : k = p⁻¹ * q.1 := by rw [h, inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem hp.1) q.2
    exact ⟨⟨p, hp.1⟩, ⟨k, hk'⟩, Subtype.ext h, hp.2, hk⟩
  have hI' : Iwa (A.uQ ε (Set.univ : Set ↥sᶜ)) (A.uK ε ↥sᶜ) := fun m => by
    obtain ⟨P, K₁, h, hP, hK₁⟩ := hdec (jQ A ε m)
    refine ⟨piQ A ε hσ P, ((pull_mem A ε hσ P.1).1 ⟨P.2, hP⟩).2, piQ A ε hσ K₁, pi_K A ε hσ K₁ hK₁, ?_⟩
    rw [← map_mul, ← h, pi_j]
  refine ⟨piQ A ε hσ, jQ A ε, c₀ A ε s, ⟨pi_cont A ε hσ, j_cont A ε, pi_j A ε hσ, c₀_par A ε hB hA hI, fun m => ?_,
    pi_K A ε hσ, j_K A ε, pi_Γ A ε hσ hL.iinj, j_Γ A ε⟩, ⟨pull_mem A ε hσ, fun q hq => ?_⟩, hI', fun q k hk => ?_⟩
  · simp only [c₀]
    rw [bdet_j, map_one]
    rfl
  · have hp : (q : A.U ε ι) ∈ A.uQ ε Set.univ := ((pull_mem A ε hσ q.1).2 ⟨q.2, hq⟩).2
    change (A.χ (bdet (Sum.inl '' (Set.univ : Set ι)) (q : A.U ε ι).1) : ℂ) =
      (A.χ (bdet (Sum.inl '' s) (q : A.U ε ι).1) : ℂ) *
        (A.χ (bdet (Sum.inl '' (Set.univ : Set ↥sᶜ)) (piQ A ε hσ q).1) : ℂ)
    rw [bdet_split A ε hσ q hp, map_mul, Circle.coe_mul]
  · obtain ⟨P, K₁, h, hP, hK₁⟩ := hdec q
    have e1 : (q : A.U ε ι) * k = (P : A.U ε ι) * ((K₁ : A.U ε ι) * k) := by
      rw [h, Subgroup.coe_mul, mul_assoc]
    have hkk : (K₁ : A.U ε ι) * k ∈ A.uK ε ι := mul_mem hK₁ hk
    change A.uH ε Set.univ ((q : A.U ε ι) * k) - A.uH ε s ((q : A.U ε ι) * k) = _
    rw [e1, uH_pk A ε Set.univ hB hE hL hK hIu _ hP _ hkk, uH_pk A ε s hB hE hL hK hIs _ P.2 _ hkk, h, map_mul,
      uH_pk A ε Set.univ hB hE hL hK' hI' _ ((pull_mem A ε hσ P.1).1 ⟨P.2, hP⟩).2 _ (pi_K A ε hσ K₁ hK₁),
      bdet_split A ε hσ P hP, hL.lgmul]
    ring
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
