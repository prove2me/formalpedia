-- Prove2me | solution 1 for GlobalTheory.NL.Model.exists_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:38.506866+00:00
-- url     : https://prove2.me/submissions/e328b550-7618-403a-b257-b2f63ad787da

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_zetaQ_mem
import Theorems.Thm_GlobalTheory_NL_Model_unramifiedSubfield_le_cyclotomicExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
namespace GlobalTheory.NL.Model
theorem _root_.solution (h : Good K s LL) (i : Let K) :
    ∃ (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), Pt H h i ζ τ := by
  let e : ↥(K0 K) →ₐ[ℚ_[l]] Om l := LL.1.val.comp ((H.W K s LL h).emb i)
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l, ∀ x : ↥(K0 K), φ ⟨x, unramifiedSubfield_le_cyclotomicExt K s x.2⟩ = e x := by
    letI : Algebra ↥(K0 K) ↥(Ks K s) := (IntermediateField.inclusion (unramifiedSubfield_le_cyclotomicExt K s)).toRingHom.toAlgebra
    haveI : IsScalarTower ℚ_[l] ↥(K0 K) ↥(Ks K s) := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.IsAlgebraic ↥(K0 K) ↥(Ks K s) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
    obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := ℚ_[l]) (L := ↥(K0 K)) (M := Om l) (E := ↥(Ks K s)) e
    exact ⟨φ, fun x => DFunLike.congr_fun hφ x⟩
  let τs : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := φ.codRestrict LL.1.toSubalgebra (h.2.2.2 φ)
  refine ⟨τs ⟨_, zetaQ_mem P K s⟩, τs.comp (IntermediateField.inclusion h.2.2.1), τs, ⟨?_, ?_⟩, ?_⟩
  · intro x y hy
    obtain rfl : y = ⟨x, unramifiedSubfield_le_cyclotomicExt K s x.2⟩ := Subtype.ext hy
    exact Subtype.ext (hφ x)
  · intro y hy
    obtain rfl : y = ⟨_, zetaQ_mem P K s⟩ := Subtype.ext hy
    rfl
  · intro x y hy
    obtain rfl : y = ⟨x, h.2.2.1 x.2⟩ := Subtype.ext hy
    rfl
end GlobalTheory.NL.Model
