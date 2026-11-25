-- Prove2me | solution 1 for GlobalTheory.ToricData.weilQkIs_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:17.119418+00:00
-- url     : https://prove2.me/submissions/b2b094d1-ef23-4b8c-a667-23bd2fc3a9b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Theorems.Thm_GlobalTheory_ToricData_sec_f_eq
import Theorems.Thm_GlobalTheory_ToricData_secVal_of_phiRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]
namespace GlobalTheory.ToricData
theorem _root_.solution {n : ℕ} (p p' : QkPt (toricPre K X q) F n) (t t') (hp : p.g = pt q F t) (hp' : p'.g = pt q F t') :
    WeilQkIs (toricPre K X q) F n p p'
      ((t (Multiplicative.ofAdd (show X from p'.y)) * (t' (Multiplicative.ofAdd (show X from p.y)))⁻¹ : Fˣ) : F) := by
  intro w w' _ _ s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ β j
  obtain ⟨a, ha⟩ := exists_isConst w
  obtain ⟨c, rfl⟩ := unitOn_bijective.2 a
  obtain ⟨a', ha'⟩ := exists_isConst w'
  obtain ⟨c', rfl⟩ := unitOn_bijective.2 a'
  change X at β
  let y : X := p.y
  let y' : X := p'.y
  have e₁ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₁ (β - y - y') (β - y - y' + y') rfl
  have e₂ := secVal_of_phiRel q F p t hp w c ha h₂ (β - y - y' + y') β (show β = β - y - y' + y' + y by abel)
  have e₃ := secVal_of_phiRel q F p t hp w c ha h₃ (β - y - y') (β - y - y' + y) rfl
  have e₄ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₄ (β - y - y' + y) β (show β = β - y - y' + y + y' by abel)
  have e : secVal (s₂.s β) = (constUnit q F (t (Multiplicative.ofAdd y') * (t' (Multiplicative.ofAdd y))⁻¹)).val *
      secVal (s₄.s β) := by
    rw [e₂, e₄, e₁, e₃, _root_.mul_assoc, _root_.mul_assoc, mul_left_comm (Units.val _), ← Units.val_mul, ← Units.val_mul,
      ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 3
    simp only [ofAdd_add, map_mul]
    generalize t (Multiplicative.ofAdd (β - y - y')) = A
    generalize t' (Multiplicative.ofAdd (β - y - y')) = B
    generalize t (Multiplicative.ofAdd y') = C
    generalize t' (Multiplicative.ofAdd y) = D
    ext
    push_cast
    field_simp
  refine (sec_f_eq (s₂.s β) j).trans ?_
  rw [e, map_mul, sec_f_eq (s₄.s β) j]
  rfl
end GlobalTheory.ToricData
