-- Prove2me | solution 1 for GlobalTheory.familyUnif_lattice_genus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:10.197642+00:00
-- url     : https://prove2.me/submissions/f5321013-3cef-41c6-a7bf-6394701f0140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TateIsoExistsLiftOfTwoData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompatibleNormTowerProfiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsInverseUnitTower
import Theorems.Thm_GlobalTheory_exists_inverse_unit_tower
import Theorems.Thm_GlobalTheory_level_smul_mem_half
import Theorems.Thm_GlobalTheory_T_exists_compatible_norm_tower_profinite
import Theorems.Thm_GlobalTheory_familyUnif_lattice_similar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - D.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6, -⟩ := familyUnif_lattice_similar E H D l Xo σ g ty U i P hP
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := exists_inverse_unit_tower ν h3 h4
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_compatible_norm_tower_profinite E H l κ hκ2 hκ3
  have hinv : ∀ n : ℕ, 0 < n → ∃ r c : 𝓞 E, r * s n = 1 + n * c := by
    intro n hn
    obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    have hd' : (κ n : 𝓞 E) * (ν n : 𝓞 E) - 1 = (n : 𝓞 E) * (d : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hd
    exact ⟨(ν n : 𝓞 E) * H.bar (s n), (ν n : 𝓞 E) * c + d, by linear_combination (ν n : 𝓞 E) * hc + hd'⟩
  refine ⟨fun n => s n • f n, fun n m hn hm a => ?_, fun n hn => ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩,
    fun n hn a a' => ?_, fun a ha => ?_⟩
  · obtain ⟨e, he⟩ := h1 n m hn hm a
    obtain ⟨c, hc⟩ := hs2 n m hn hm
    have hc' : s (n * m) = s n + n * c := by linear_combination hc
    refine ⟨c • f n a + s (n * m) • e, ?_⟩
    simp only [LinearMap.smul_apply]
    rw [he, hc', ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · rintro ⟨e, he⟩
    obtain ⟨r, c, hrc⟩ := hinv n hn
    rw [← (h2 n hn).1 a]
    refine ⟨r • e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul (𝓞 E)] at he
    have h : (r * s n) • f n a = r • (n : 𝓞 E) • e := by rw [mul_smul, he]
    rw [hrc] at h
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    linear_combination (norm := module) h
  · rintro ⟨e, rfl⟩
    exact ⟨(s n • f n) e, by rw [map_nsmul]⟩
  · obtain ⟨a, e, he⟩ := (h2 n hn).2 a'
    obtain ⟨r, c, hrc⟩ := hinv n hn
    refine ⟨r • a, e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_comm, hrc, he, ← Nat.cast_smul_eq_nsmul (𝓞 E),
      ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    obtain ⟨k, hk⟩ := h5 n hn (s n • a) (s n • a')
    have hc' : H.bar (s n) * s n = (κ n : 𝓞 E) + (n : 𝓞 E) * c := by linear_combination hc
    have e1 : D.EF (s n • a) (s n • a') = κ n * D.EF a a' + n * D.EF a (c • a') := by
      rw [D.adj, smul_smul, hc', add_smul, mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul, map_add,
        map_nsmul, map_zsmul, smul_eq_mul, nsmul_eq_mul]
    simp only [LinearMap.smul_apply, ← map_smul]
    rw [e1] at hk
    refine ⟨k + d * D.EF a a' + ν n * D.EF a (c • a'), ?_⟩
    linear_combination hk + D.EF a a' * hd
  · obtain ⟨e, he⟩ := h6 a ha
    obtain ⟨e', he'⟩ := level_smul_mem_half l hs3 ha
    refine ⟨e + f l.M e', ?_⟩
    have h : s l.M • a = a + l.M • e' := by rw [← he', sub_smul, one_smul, add_sub_cancel]
    rw [LinearMap.smul_apply, ← map_smul, h, map_add, map_nsmul, he, smul_add, add_assoc]
end GlobalTheory
