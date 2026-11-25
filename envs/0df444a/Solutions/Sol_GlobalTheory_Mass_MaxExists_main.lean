-- Prove2me | solution 1 for GlobalTheory.Mass.MaxExists.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:28:17.102981+00:00
-- url     : https://prove2.me/submissions/1bd4f61f-8f52-4c8e-9359-0e2e3f5b2283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormal
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_eq_one
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_finrank_of_ortho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isLattice_of_ortho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isUnimodular_of_ortho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.MaxExists
open NumberField Matrix in
open scoped ENNReal Classical in
private lemma isIntLat_of_isUnimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K M)
    (hU : _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M) : _root_.GlobalTheory.Mass.IsIntLat h M := by
  unfold _root_.GlobalTheory.Mass.IsIntLat
  refine ⟨hL, ?_⟩
  unfold _root_.Formalism.HermitianLatticesTheory.IsIntegralLat
  intro x hx y hy
  unfold _root_.Formalism.HermitianLatticesTheory.IsUnimodular at hU
  have hy' : y ∈ _root_.Formalism.HermitianLatticesTheory.dual h M := by rw [hU]; exact hy
  exact (_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M y).1 hy' x hx
end GlobalTheory.Mass.MaxExists
end

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.MaxExists
open NumberField Matrix
open scoped ENNReal Classical
namespace GlobalTheory.Mass.MaxExists
namespace _root_.GlobalTheory.Mass.MaxExists
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M → ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M → _root_.GlobalTheory.Mass.IsMaxLat h M ∧ _root_.GlobalTheory.Mass.badP h M = ∅ ∧ _root_.GlobalTheory.Mass.lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h M n → Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M ∧ Module.finrank K V = n) := by
  intro K V _ _ _ _ _ _ _ _ h hK hS hN
  have D := fun M hM => _root_.GlobalTheory.Mass.DiscOrder.main K V h hK hS hN M hM
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ n : ℕ, ∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M →
        _root_.GlobalTheory.Mass.discN h M = n →
        ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M' := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro M hM hn
        by_cases hmax : ∀ N : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h N → M ≤ N → N = M
        · exact ⟨M, by unfold _root_.GlobalTheory.Mass.IsMaxLat; exact ⟨hM, hmax⟩, le_rfl⟩
        · push_neg at hmax
          obtain ⟨N, hNi, hMN, hne⟩ := hmax
          obtain ⟨hidx0, hdisc⟩ := (D M hM).2.2.1 N hNi hMN
          have hidx1 : _root_.GlobalTheory.Mass.idxN N M ≠ 1 := by
            intro h1
            exact hne (le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1) hMN)
          have hNpos : 0 < _root_.GlobalTheory.Mass.discN h N :=
            Nat.pos_of_ne_zero (D N hNi).1
          have hlt : _root_.GlobalTheory.Mass.discN h N < n := by
            rw [← hn, hdisc]
            have h2 : 2 ≤ _root_.GlobalTheory.Mass.idxN N M := by omega
            have h4 : 1 < _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
              Nat.one_lt_pow (by norm_num) (by omega)
            calc _root_.GlobalTheory.Mass.discN h N
                = _root_.GlobalTheory.Mass.discN h N * 1 := (mul_one _).symm
              _ < _root_.GlobalTheory.Mass.discN h N * _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
                  Nat.mul_lt_mul_of_pos_left h4 hNpos
          obtain ⟨M', hM', hNM'⟩ := ih _ hlt N hNi rfl
          exact ⟨M', hM', hMN.trans hNM'⟩
    exact fun M hM => key _ M hM rfl
  · intro M hL hU
    have hI := isIntLat_of_isUnimodular hL hU
    have hD1 : _root_.GlobalTheory.Mass.discN h M = 1 := ((D M hI).2.1).2 hU
    have hbad : _root_.GlobalTheory.Mass.badP h M = ∅ := by
      unfold _root_.GlobalTheory.Mass.badP
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hP
      refine (D M hI).2.2.2.2.1 P hP ?_
      rw [hD1, Nat.cast_one]
      exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
    refine ⟨?_, hbad, ?_⟩
    · unfold _root_.GlobalTheory.Mass.IsMaxLat
      refine ⟨hI, fun N hNi hMN => ?_⟩
      obtain ⟨_, hdisc⟩ := (D M hI).2.2.1 N hNi hMN
      rw [hD1] at hdisc
      have h1 : _root_.GlobalTheory.Mass.idxN N M ^ 2 = 1 :=
        Nat.eq_one_of_mul_eq_one_left hdisc.symm
      have h1' : _root_.GlobalTheory.Mass.idxN N M = 1 := by
        simpa using h1
      exact le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1') hMN
    · unfold _root_.GlobalTheory.Mass.lamMax
      rw [hbad]
      exact finprod_mem_empty
  · intro M n hO
    exact ⟨_root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.isUnimodular_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.finrank_of_ortho hO⟩
end _root_.GlobalTheory.Mass.MaxExists
end GlobalTheory.Mass.MaxExists
