-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:29.965676+00:00
-- url     : https://prove2.me/submissions/fb400d0d-073b-470d-a536-440d8c187067

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_sc
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_common_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (hC : CxSt) {F F' : C ⥤ CommAlgCat.{0} R} (ρ : ∀ T, F.obj T →ₐ[R] F'.obj T)
    (hρ : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), ρ T' (mp F φ b) = mp F' φ (ρ T b))
    (g : ∀ T, F.obj T) (hg : ∀ (T T' : C) (φ : T ⟶ T'), mp F φ (g T) = g T')
    (loc1 : ∀ T (y' : F'.obj T), ∃ (N : ℕ) (y : F.obj T), ρ T y = ρ T (g T) ^ N * y')
    (loc2 : ∀ T (y : F.obj T), ρ T y = 0 → ∃ N : ℕ, g T ^ N * y = 0)
    (n : ℕ) [Finite (Fin (n + 1) ⥤ C)] [Finite (Fin (n + 2) ⥤ C)]
    (hex : ∀ z' : Cn F' (n + 1), dn F' (n + 1) z' = 0 → ∃ y', dn F' n y' = z')
    (z : Cn F (n + 1)) (hz : dn F (n + 1) z = 0) :
    ∃ (N : ℕ) (y : Cn F n), dn F n y = sc F (fun T ↦ g T ^ N) (n + 1) z := by
  set m := nat ρ hρ with hm
  have comm : ∀ k (w : Cn F k), pulln m (k + 1) (dn F k w) = dn F' k (pulln m k w) := fun k w ↦
    LinearMap.congr_fun ((hC R C F).2 C F' m k) w
  have hg' : ∀ (N : ℕ) (T T' : C) (φ : T ⟶ T'), mp F φ (g T ^ N) = g T' ^ N := fun N T T' φ ↦ by
    rw [map_pow, hg]
  have hg'' : ∀ (N : ℕ) (T T' : C) (φ : T ⟶ T'), mp F' φ (ρ T (g T) ^ N) = ρ T' (g T') ^ N :=
    fun N T T' φ ↦ by rw [map_pow, ← hρ, hg]
  obtain ⟨y', hy'⟩ := hex (pulln m (n + 1) z) (by rw [← comm, hz, map_zero])
  obtain ⟨N, hN⟩ := common_exp (J := Fin (n + 1) ⥤ C)
    (fun c N ↦ ∃ y : F.obj (c.obj (Fin.last n)),
      ρ _ y = ρ _ (g (c.obj (Fin.last n))) ^ N * y' c) fun c ↦ by
    obtain ⟨N, y, hy⟩ := loc1 _ (y' c)
    refine ⟨N, fun M hM ↦ ⟨g _ ^ (M - N) * y, ?_⟩⟩
    rw [map_mul, hy, map_pow, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hM]
  choose y hy using hN
  have e1 : pulln m n y = sc F' (fun T ↦ ρ T (g T) ^ N) n y' := funext hy
  have e2 : pulln m (n + 1) (dn F n y - sc F (fun T ↦ g T ^ N) (n + 1) z) = 0 := by
    rw [map_sub, comm, e1, dn_sc F' _ (hg'' N), hy', sub_eq_zero]
    funext c
    change ρ _ (g (c.obj (Fin.last (n + 1)))) ^ N * ρ _ (z c) = ρ _ (g (c.obj (Fin.last (n + 1))) ^ N * z c)
    rw [map_mul, map_pow]
  obtain ⟨M, hM⟩ := common_exp (J := Fin (n + 2) ⥤ C)
    (fun c M ↦ g (c.obj (Fin.last (n + 1))) ^ M *
      (dn F n y - sc F (fun T ↦ g T ^ N) (n + 1) z) c = 0) fun c ↦ by
    obtain ⟨M, hM⟩ := loc2 _ _ (congrFun e2 c)
    have hM' : g (c.obj (Fin.last (n + 1))) ^ M *
      (dn F n y - sc F (fun T ↦ g T ^ N) (n + 1) z) c = 0 := hM
    refine ⟨M, fun K hK ↦ ?_⟩
    rw [← Nat.sub_add_cancel hK, pow_add, _root_.mul_assoc, hM', mul_zero]
  refine ⟨M + N, sc F (fun T ↦ g T ^ M) n y, ?_⟩
  rw [dn_sc F _ (hg' M)]
  funext c
  have := hM c
  rw [Pi.sub_apply, mul_sub, sub_eq_zero] at this
  refine this.trans ?_
  change g (c.obj (Fin.last (n + 1))) ^ M * (g (c.obj (Fin.last (n + 1))) ^ N * z c) =
    g (c.obj (Fin.last (n + 1))) ^ (M + N) * z c
  rw [pow_add, _root_.mul_assoc]
end GlobalTheory.CompanionTheory.AffAcyc
