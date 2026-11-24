-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.moved_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:31.827292+00:00
-- url     : https://prove2.me/submissions/55779901-3ecf-4787-bc26-d18243b8f81d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {S S' W : Scheme.{0}} {t : W ⟶ S} {t' : W ⟶ S'}
  {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
  {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left} {Y Y' N N' V V' : Scheme.{0}} {M : LB N} {M' : LB N'}
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB)
    {c₀ : Y ⟶ A.left} {n : A.left ⟶ Y} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)}
    {c₁ : Y' ⟶ A'.left} {n₁ : A'.left ⟶ Y'} (hn₁ : c₁ ≫ n₁ = 𝟙 _) {q' : Y' ⟶ N'} {w' : LB.Iso (L'.pull c₁) (M'.pull q')}
    {Ψ : N' ⟶ N} {wM : LB.Iso M' (M.pull Ψ)} (hn : n ≫ c₀ = 𝟙 _) (hΦ : (c₁ ≫ Φ) ≫ n ≫ q = q' ≫ Ψ)
    {v₂ : LB.Iso (L'.pull c₁) (L.pull (c₁ ≫ Φ))}
    (hsq : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (z : Z) (j : M.ι) (j' : M'.ι) (i : L.ι) (i' : L'.ι),
        Ψ (q' (f z)) ∈ M.U j → q' (f z) ∈ M'.U j' → (c₁ ≫ Φ) (f z) ∈ L.U i → c₁ (f z) ∈ L'.U i' →
        isoVal w (f ≫ (c₁ ≫ Φ) ≫ n) z j i * isoVal v₂ f z i i' = gw wM (f ≫ q') z j j' * isoVal w' f z j' i')
    {v : LB.Iso L' (L.pull Φ)}
    (hv : ∀ (Z : Scheme.{0}) (f : Z ⟶ A'.left) (z : Z) (j : L.ι) (i : L'.ι),
      Φ (f z) ∈ L.U j → f z ∈ L'.U i → gw v f z j i = isoVal v₂ (f ≫ n₁) z j i)
    {m : V ⟶ Y} {h : V ⟶ (Over.mk t ⊗ A).left} {m' : V' ⟶ Y'} {h' : V' ⟶ (Over.mk t' ⊗ A').left} {Ξ : V' ⟶ V}
    (x₁ : (Ξ ≫ h) ≫ ω = h') (x₂ : Ξ ≫ m = m' ≫ (c₁ ≫ Φ) ≫ n) {k : ℕ}
    {s' : LB.Sec (LPow A' L' k (Over.mk t'))} {s : LB.Sec (LPow A L k (Over.mk t))} (hs : Moved v ω s' s)
    {σ : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => m ≫ q) (fun _ => (k : ℤ)))}
    {σ' : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => m' ≫ q') (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L M c₀ q w m k (snd (Over.mk t) A).left h s (m ≫ q) (𝟙 _) σ)
    (H' : GeneratorPullback.IsoRelM L' M' c₁ q' w' m' k (snd (Over.mk t') A').left h' s' (m' ≫ q') (𝟙 _) σ')
    (Z : Scheme.{0}) (r : Z ⟶ V') (z : Z) (p : Fin 1 → M.ι) (p' : Fin 1 → M'.ι)
    (hp : ∀ κ, Ψ ((m' ≫ q') (r z)) ∈ M.U (p κ)) (hp' : ∀ κ, (m' ≫ q') (r z) ∈ M'.U (p' κ)) :
    gs (r ≫ Ξ) z (LB.wchart M (fun _ : Fin 1 => m ≫ q) p) (σ.f p) =
      (∏ κ : Fin 1, gw wM (r ≫ m' ≫ q') z (p κ) (p' κ) ^ (k : ℤ)).val *
        gs r z (LB.wchart M' (fun _ : Fin 1 => m' ≫ q') p') (σ'.f p') := by
  have H₀ := H
  have H₀' := H'
  unfold GeneratorPullback.IsoRelM at H₀ H₀'
  have PH := (isoRelM_iff w m k h H₀.1 (𝟙 V) H₀.2.1 s σ).1 H
  have PH' := (isoRelM_iff w' m' k h' H₀'.1 (𝟙 V') H₀'.2.1 s' σ').1 H'
  obtain ⟨i₁, hi₁⟩ := exists_chart hL (c₀ (m (Ξ (r z))))
  obtain ⟨i', hi'⟩ := exists_chart hL' (c₁ (m' (r z)))
  simp only [Category.assoc] at hΦ x₂ x₁
  have eq_q : Ξ ≫ m ≫ q = m' ≫ q' ≫ Ψ := by
    rw [← Category.assoc, x₂]
    simp only [Category.assoc, hΦ]
  have eq_c : Ξ ≫ m ≫ c₀ = m' ≫ c₁ ≫ Φ := by
    rw [← Category.assoc, x₂]
    simp only [Category.assoc, hn, Category.comp_id]
  have eq_h' : h' ≫ (snd (Over.mk t') A').left ≫ n₁ = m' := by
    rw [← Category.assoc, H₀'.1, Category.assoc, hn₁, Category.comp_id]
  have eq_R : ((r ≫ Ξ) ≫ h) ≫ ω = r ≫ h' := by
    simp only [Category.assoc, x₁]
  have m_q : (Ξ ≫ m ≫ q) (r z) ∈ M.U (p 0) := by
    rw [eq_q]
    exact hp 0
  have m_snd : (h ≫ (snd (Over.mk t) A).left) (Ξ (r z)) ∈ L.U i₁ := by
    rw [H₀.1]
    exact hi₁
  have m_h' : (h' ≫ (snd (Over.mk t') A').left) (r z) ∈ L'.U i' := by
    rw [H₀'.1]
    exact hi'
  have m_snd' : ((((r ≫ Ξ) ≫ h) ≫ ω) ≫ (snd (Over.mk t') A').left) z ∈ L'.U i' := by
    rw [eq_R, Category.assoc]
    exact m_h'
  have m_c : (m' ≫ c₁ ≫ Φ) (r z) ∈ L.U i₁ := by
    rw [← eq_c]
    exact hi₁
  have m_v1 : (h' ≫ (snd (Over.mk t') A').left ≫ Φ) (r z) ∈ L.U i₁ := by
    rw [← Category.assoc, H₀'.1, Category.assoc]
    exact m_c
  have E1 := PH Z (r ≫ Ξ) z (p 0) i₁ m_q hi₁
  have E2 := hs Z ((r ≫ Ξ) ≫ h) z i₁ i' m_snd m_snd'
  rw [eq_R] at E2
  have E3 := PH' Z r z (p' 0) i' (hp' 0) hi'
  have E4 := hsq Z (r ≫ m') z (p 0) (p' 0) i₁ i' (hp 0) (hp' 0) m_c hi'
  have E5 := hv Z ((r ≫ h') ≫ (snd (Over.mk t') A').left) z i₁ i' m_v1 m_h'
  have eq_m : ((r ≫ h') ≫ (snd (Over.mk t') A').left) ≫ n₁ = r ≫ m' := by
    simp only [Category.assoc]
    rw [eq_h']
  rw [eq_m] at E5
  have eq_W : (r ≫ m') ≫ (c₁ ≫ Φ) ≫ n = (r ≫ Ξ) ≫ m := by
    simp only [Category.assoc]
    rw [x₂]
  have eq_g : (r ≫ m') ≫ q' = r ≫ m' ≫ q' := Category.assoc _ _ _
  rw [eq_W, eq_g] at E4
  have hp0 : p = fun _ => p 0 := funext fun κ => congrArg p (Subsingleton.elim κ 0)
  have hp0' : p' = fun _ => p' 0 := funext fun κ => congrArg p' (Subsingleton.elim κ 0)
  have L1 : gs (r ≫ Ξ) z (M.wchart (fun _ => m ≫ q) p) (σ.f p) = powVal σ ((r ≫ Ξ) ≫ 𝟙 V) z (p 0) := by
    rw [Category.comp_id, hp0]
    rfl
  have L2 : gs r z (M'.wchart (fun _ => m' ≫ q') p') (σ'.f p') = powVal σ' (r ≫ 𝟙 V') z (p' 0) := by
    rw [Category.comp_id, hp0']
    rfl
  have E6 : isoVal w ((r ≫ Ξ) ≫ m) z (p 0) i₁ ^ (k : ℤ) * isoVal v₂ (r ≫ m') z i₁ i' ^ (k : ℤ) =
      gw wM (r ≫ m' ≫ q') z (p 0) (p' 0) ^ (k : ℤ) * isoVal w' (r ≫ m') z (p' 0) i' ^ (k : ℤ) := by
    rw [← mul_zpow, ← mul_zpow, E4]
  rw [Fin.prod_univ_one, L1, L2, E1, E2, E3, E5, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, E6]
end GlobalTheory.ThetaBaseChange
