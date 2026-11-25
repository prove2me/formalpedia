-- Prove2me | solution 1 for GlobalTheory.SecPow.exists_pow_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:21:42.18022+00:00
-- url     : https://prove2.me/submissions/9928937c-5208-4727-99dc-397214152791

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowSection
import Theorems.Thm_GlobalTheory_SecPow_eq_of_preimage_eq
import Theorems.Thm_GlobalTheory_SecPow_app_rs
import Theorems.Thm_GlobalTheory_SecPow_exists_lift_pow
import Theorems.Thm_GlobalTheory_SecPow_exists_pow_eq
import Theorems.Thm_GlobalTheory_SecPow_exists_finite_affine_cover
import Theorems.Thm_GlobalTheory_SecPow_basicOpen_rs_eq
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_compat
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_existsUnique_of_local
import Theorems.Thm_GlobalTheory_AbLaw_isLB_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.SecPow
variable {X X' : Scheme.{0}}
namespace GlobalTheory.SecPow
theorem _root_.solution : ∀ (X X' : Scheme.{0}) (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β] [CompactSpace X] [QuasiSeparatedSpace X], (∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0) → ∀ H : LB X, H.IsLB → ∀ (s₀ : LB.Sec (H.pull β)) (D : X.Opens), β ⁻¹ᵁ D = nonzeroLocus s₀ → ∀ t : SecOn H D, SecOn.pull H β D t = GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D) → ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : LB.Sec (pw H n), nonzeroLocus σ = D := by
  intro X X' β _ _ _ _ hsq H hH s₀ D hD t ht
  obtain ⟨I, _, V, c, hV, hc, hcov⟩ := exists_finite_affine_cover hH
  let s (a : I) : Γ(X', β ⁻¹ᵁ V a) := rs X' (le_pull H β (hc a)) (s₀.f fun _ => c a)
  let τ (a : I) : Γ(X, V a ⊓ D) :=
    rs X (le_inf inf_le_right (inf_le_left.trans (hc a))) (GlobalTheory.LB.coord t (c a))
  have hs (a : I) : X'.basicOpen (s a) = β ⁻¹ᵁ (V a ⊓ D) :=
    (basicOpen_rs_eq s₀ (fun _ => c a) (le_pull H β (hc a))).trans
      (congrArg (β ⁻¹ᵁ V a ⊓ ·) hD.symm)
  have hτ (a : I) : (β.app _).hom (τ a) = rs X' (β.preimage_mono inf_le_left) (s a) := by
    have e := congrArg (fun z => rs X' (le_inf (β.preimage_mono inf_le_right)
      (le_pull H β (inf_le_left.trans (hc a))) :
        β ⁻¹ᵁ (V a ⊓ D) ≤ β ⁻¹ᵁ D ⊓ (H.pull β).U fun _ => c a) (GlobalTheory.LB.coord z fun _ => c a)) ht
    rw [app_rs, rs_rs]
    exact ((GlobalTheory.LB.resG_appLE β _ _ _).symm.trans e).trans (rs_rs _ _ _)
  choose k₀ hk₀ using fun a => exists_lift_pow β hsq (hV a) inf_le_left (τ a) (s a) (hs a) (hτ a)
  obtain ⟨k₁, hk₁⟩ := (Set.finite_range k₀).bddAbove
  choose σ hσs hστ using fun a => hk₀ a (k₁ + 1) ((hk₁ ⟨a, rfl⟩).trans (Nat.le_succ _))
  have hbo (a : I) : X.basicOpen (σ a) = V a ⊓ D := by
    refine eq_of_preimage_eq β ((Scheme.preimage_basicOpen β _).trans ?_)
    rw [← hs, ← X'.basicOpen_pow (s a) (Nat.succ_pos k₁)]
    exact congrArg X'.basicOpen (hσs a)
  let g (a b : I) : Γ(X, V a ⊓ V b) := rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b)).val
  have key (p : I × I) : ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → rs X inf_le_left (σ p.1) ^ l =
      (g p.1 p.2 ^ (k₁ + 1) * rs X inf_le_right (σ p.2)) ^ l := by
    obtain ⟨a, b⟩ := p
    have hsm : (β.app _).hom (g a b ^ (k₁ + 1) * rs X inf_le_right (σ b) -
        rs X inf_le_left (σ a)) = 0 := by
      have e := GlobalTheory.LB.sec_rel s₀ (fun _ => c a) (fun _ => c b) (W := β ⁻¹ᵁ (V a ⊓ V b))
        (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b)))
        (le_inf (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b))))
      erw [GlobalTheory.LB.resG_pull_g] at e
      rw [map_sub, map_mul, map_pow, app_rs, app_rs, app_rs, hσs, hσs, map_pow, map_pow, rs_rs, rs_rs,
        ← mul_pow, sub_eq_zero]
      exact congrArg (· ^ (k₁ + 1)) e.symm
    refine exists_pow_eq (O := V a ⊓ V b ⊓ D)
      (QuasiSeparatedSpace.inter_isCompact _ _ (V a).isOpen (hV a).isCompact (V b).isOpen
        (hV b).isCompact) inf_le_left _ _ (hsq _ _ _ hsm hsm) ?_ ?_
    · erw [Scheme.basicOpen_res]
      rw [hbo]
      exact inf_le_inf_left _ inf_le_right
    · have ea := congrArg (rs X (inf_le_inf_right D inf_le_left : V a ⊓ V b ⊓ D ≤ V a ⊓ D)) (hστ a)
      have eb := congrArg (rs X (inf_le_inf_right D inf_le_right : V a ⊓ V b ⊓ D ≤ V b ⊓ D)) (hστ b)
      rw [rs_rs, map_pow, rs_rs] at ea eb
      rw [map_mul, map_pow, rs_rs, rs_rs, rs_rs, ea, eb, ← mul_pow]
      exact congrArg (· ^ (k₁ + 1)) (SecOn.compat t (c a) (c b) _ _ _)
  choose l₀ hl₀ using key
  obtain ⟨l₁, hl₁⟩ := (Set.finite_range l₀).bddAbove
  obtain ⟨u, hu, -⟩ := SecOn.existsUnique_of_local (V := ⊤)
    (isLB_pw hH (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)) V (fun _ => le_top) hcov c hc
    (fun a => σ a ^ (l₁ + 1)) fun a b => by
      have e := hl₀ (a, b) (l₁ + 1) ((hl₁ ⟨(a, b), rfl⟩).trans (Nat.le_succ _))
      rw [mul_pow, ← pow_mul] at e
      rw [map_pow, map_pow]
      refine e.trans (congrArg (· * _) ?_)
      change _ = rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b) ^ (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)).val
      rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  refine ⟨(k₁ + 1) * (l₁ + 1), Nat.succ_le_of_lt (by positivity), SecOn.topEquiv _ u, ?_⟩
  have hloc (a : I) : V a ⊓ nonzeroLocus (SecOn.topEquiv _ u) = V a ⊓ D := by
    rw [← basicOpen_rs_eq (SecOn.topEquiv _ u) (c a) (hc a), ← hbo,
      ← X.basicOpen_pow (σ a) (Nat.succ_pos l₁)]
    exact congrArg X.basicOpen ((rs_rs _ _ _).trans (hu a))
  ext x
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov (Set.mem_univ x))
  have e := SetLike.ext_iff.1 (hloc a) x
  exact ⟨fun h => (e.1 ⟨ha, h⟩).2, fun h => (e.2 ⟨ha, h⟩).2⟩
end GlobalTheory.SecPow
