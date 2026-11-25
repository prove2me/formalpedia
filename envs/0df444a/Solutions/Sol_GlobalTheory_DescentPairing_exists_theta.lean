-- Prove2me | solution 1 for GlobalTheory.DescentPairing.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:50.287969+00:00
-- url     : https://prove2.me/submissions/fecaff3d-8546-415c-9bec-a318f3807c74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
import Theorems.Thm_GlobalTheory_DescentPairing_exists_frame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DescentPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)
namespace GlobalTheory.DescentPairing
theorem _root_.solution {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ A) (hy : y ^ n = 1) :
    ∃ θ : ThetaGrp A L.L n T, θ.pt = y ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, thetaVal θ t a z J = cubN (cubV c z J) n 1 (t ≫ y) a * s := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, y.left] ![(n : ℤ), -n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ y) (snd T A) n
  have e₁ : (fst T A ≫ y) ^ n = 1 :=
    (map_pow (preHom (fst T A)) y n).symm.trans (by rw [hy]; exact map_one _)
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A y).left])
    (ε' := ![(n : ℤ), -n]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A y = (fst T A ≫ y) * snd T A := rfl
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.pullGen L.L _ _ σ (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨⟨y, u, hu⟩, rfl, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]
end GlobalTheory.DescentPairing
