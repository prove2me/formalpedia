-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:53.955564+00:00
-- url     : https://prove2.me/submissions/40dca6d7-6900-449e-a5ba-9a760b9d2b21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_GlobalTheory_VeryAmplePow_exists_pull
import Theorems.Thm_GlobalTheory_VeryAmplePow_value_sval
import Theorems.Thm_GlobalTheory_VeryAmplePow_span_sval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {a : ℤ} {T : Over S} {I : Type} [Fintype I] (b : I → LB.Sec (LPow A L a T)) (T' : Over S) (h : T' ⟶ T)
    (hb : ∀ b' : I → LB.Sec (LPow A L a T'), (∀ i, IsPullSec A L a (h ▷ A) (whiskerRight_snd h A) (b i) (b' i)) →
      Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L a T')) = ⊤)
    (s : LB.Sec (LPow A L a T')) : ∃ c : I → Γ(T'.left, ⊤), ∀ (x : T' ⟶ A) (g : T'.left ⟶ (T ⊗ A).left),
      g ≫ (fst T A).left = h.left → g ≫ (snd T A).left = x.left →
      ∀ (τ : LB.Gen (LB.LinComb L (Y := T'.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))) (v : Γ(T'.left, ⊤)),
      IsValueAt A L a s x τ v → ∀ z J, Good L z J → gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val =
        ∑ i, gs (𝟙 _) z ⊤ (c i) * sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i) g z J := by
  choose b' h₁ h₂ using fun i => exists_pull (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i)
    (h ▷ A).left (fun _ => (snd T' A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  obtain ⟨c, hc⟩ := span_sval A b' (hb b' fun i j => h₁ i j _) s
  refine ⟨c, fun x g e₁ e₂ τ v hv z J hJ => ?_⟩
  have k₁ : (ptSecT A x).left ≫ (fst T' A).left = 𝟙 _ := by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have k₂ : (ptSecT A x).left ≫ (h ▷ A).left = g := by
    refine pullback.hom_ext (f := T.hom) (g := A.hom) (Eq.trans ?_ e₁.symm) (Eq.trans ?_ e₂.symm)
    · change (ptSecT A x ≫ h ▷ A ≫ fst T A).left = _
      rw [whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp]
    · change (ptSecT A x ≫ h ▷ A ≫ snd T A).left = _
      rw [whiskerRight_snd, ptSecT, lift_snd]
  rw [← value_sval A hv z hJ, hc _ _ z J hJ, k₁]
  exact Finset.sum_congr rfl fun i _ => congrArg _ ((h₂ i _ _ z J hJ).trans (by rw [k₂]))
end GlobalTheory.VeryAmplePow
