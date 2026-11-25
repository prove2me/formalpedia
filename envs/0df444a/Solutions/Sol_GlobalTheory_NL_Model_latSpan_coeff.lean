-- Prove2me | solution 1 for GlobalTheory.NL.Model.latSpan_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:49:46.069716+00:00
-- url     : https://prove2.me/submissions/fe2aa546-5025-4f62-a256-1fe5685c264e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_conv_finite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
section Series
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
private theorem conv_mem_and_vanish_below (e : PowerSeries L) (D : Submodule L M)
    {u : ℤ → M} (hu : ∀ k, u k ∈ D) {m : ℤ} (hm : ∀ k < m, u k = 0) :
    (∀ k, _root_.GlobalTheory.NL.conv e u k ∈ D) ∧
      ∀ k < m, _root_.GlobalTheory.NL.conv e u k = 0 := by
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [_root_.GlobalTheory.NL.conv,
      finsum_eq_sum _ (_root_.GlobalTheory.NL.Model.conv_finite e hm k)]
    exact Submodule.sum_mem _ fun j _ => D.smul_mem _ (hu _)
  · rw [_root_.GlobalTheory.NL.conv]
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    rw [hm _ (by omega), smul_zero]
end Series
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
end Generic
section Concrete
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
end Concrete
end GlobalTheory.NL.Model
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
open TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.NL.Model
namespace _root_.GlobalTheory.NL.Model
theorem _root_.solution {ι : Type} (ex : ι → ℤ → M)
    (D : Submodule L M) (hD : ∀ x k, ex x k ∈ D) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (f : ℤ → M) (hf : f ∈ _root_.GlobalTheory.NL.latSpan (LL := L) ex) :
    (∀ k, f k ∈ D) ∧ ∃ m : ℤ, ∀ k < m, f k = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨e, x, rfl⟩ := hg
    obtain ⟨m, hm⟩ := hs x
    obtain ⟨h1, h2⟩ := conv_mem_and_vanish_below e D (hD x) hm
    exact ⟨h1, m, h2⟩
  | zero => exact ⟨fun _ => D.zero_mem, 0, fun _ _ => rfl⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨h1, m, hm⟩ := hg
    obtain ⟨h1', m', hm'⟩ := hg'
    refine ⟨fun k => D.add_mem (h1 k) (h1' k), min m m', fun k hk => ?_⟩
    simp [hm k (lt_of_lt_of_le hk (min_le_left _ _)), hm' k (lt_of_lt_of_le hk (min_le_right _ _))]
  | smul c g _ hg =>
    obtain ⟨h1, m, hm⟩ := hg
    exact ⟨fun k => D.smul_mem c (h1 k), m, fun k hk => by simp [hm k hk]⟩
end _root_.GlobalTheory.NL.Model
end GlobalTheory.NL.Model
