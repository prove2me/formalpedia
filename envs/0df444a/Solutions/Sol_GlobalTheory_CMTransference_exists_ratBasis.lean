-- Prove2me | solution 1 for GlobalTheory.CMTransference.exists_ratBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:05.073101+00:00
-- url     : https://prove2.me/submissions/d14142d0-958d-4805-acc8-d80c69585152

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
variable {K : Type} [Field K] [NumberField K] {r : ℕ}
namespace GlobalTheory.CMTransference
theorem _root_.solution {L : Submodule (𝓞 K) (Fin r → K)} (hL : IsLattice L) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ (Fin r → K)),
      ∀ x, x ∈ L ↔ x ∈ span ℤ (Set.range b) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL.1
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let b0 := Module.finBasis ℤ L
  let v : Fin (finrank ℤ L) → Fin r → K := fun i => (b0 i : Fin r → K)
  have hli : LinearIndependent ℤ v :=
    b0.linearIndependent.map' (L.subtype.restrictScalars ℤ) (by
      rw [LinearMap.ker_eq_bot]; exact Subtype.val_injective)
  have hmem : ∀ x, x ∈ L ↔ x ∈ span ℤ (Set.range v) := by
    intro x
    constructor
    · intro hx
      have h := congrArg Subtype.val (b0.sum_repr ⟨x, hx⟩)
      simp only [AddSubmonoidClass.coe_finsetSum] at h
      rw [← h]
      exact sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _
    · intro hx
      obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
      exact sum_mem fun i _ => zsmul_mem (b0 i).2 _
  have hsp : ⊤ ≤ span ℚ (Set.range v) := by
    have key : ∀ x ∈ span K (L : Set (Fin r → K)), ∀ k : K, k • x ∈ span ℚ (Set.range v) := by
      intro x hx
      induction hx using span_induction with
      | mem x hx =>
        intro k
        obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2
          (Algebra.IsAlgebraic.isAlgebraic k)).exists_integral_multiple
        have h1 : (⟨m • k, hm⟩ : 𝓞 K) • x ∈ L := L.smul_mem _ hx
        have h2 := span_le_restrictScalars ℤ ℚ _ ((hmem _).1 h1)
        have h3 : k • x = (m : ℚ)⁻¹ • ((⟨m • k, hm⟩ : 𝓞 K) • x) := by
          ext a
          have : (m : K) ≠ 0 := by exact_mod_cast hm0
          change k * x a = (m : ℚ)⁻¹ • ((m • k) * x a)
          rw [Rat.smul_def]
          push_cast
          rw [zsmul_eq_mul]
          field_simp
        rw [h3]
        exact smul_mem _ _ h2
      | zero => intro k; simp
      | add x y _ _ hx hy => intro k; rw [smul_add]; exact add_mem (hx k) (hy k)
      | smul a x _ hx => intro k; rw [smul_smul]; exact hx _
    intro x _
    simpa using key x (hL.2 ▸ mem_top) 1
  refine ⟨_, Basis.mk ((LinearIndependent.iff_fractionRing ℤ ℚ).1 hli) hsp, fun x => ?_⟩
  rw [Basis.coe_mk]
  exact hmem x
end GlobalTheory.CMTransference
