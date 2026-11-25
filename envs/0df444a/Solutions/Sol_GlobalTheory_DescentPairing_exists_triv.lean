-- Prove2me | solution 1 for GlobalTheory.DescentPairing.exists_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:26.819201+00:00
-- url     : https://prove2.me/submissions/bea492be-4916-4121-b9a0-50cae5d97bdb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
import Theorems.Thm_GlobalTheory_DescentPairing_exists_frame
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
theorem _root_.solution {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (θ : ThetaGrp A L.L n T) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, val u (lift t a).left z J =
        cubN (cubV c z J) n 1 a (t ≫ θ.pt) * ((thetaVal θ t a z J)⁻¹ * s) := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, θ.pt.left] ![(n : ℤ) - 1, 1 - n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (snd T A) (fst T A ≫ θ.pt) n
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2)
    (φ' := ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left]) (ε' := ![1, -1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₁ : mulT A T n ≫ translPt A θ.pt = snd T A ^ n * (fst T A ≫ θ.pt) :=
        (lift_translPt θ.pt _ _).trans (mul_comm _ _)
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A θ.pt = snd T A * (fst T A ≫ θ.pt) := mul_comm (fst T A ≫ θ.pt) (snd T A)
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![(n : ℤ), -n] θ.φ)
      (LB.pullGen L.L _ _ σ (fst T A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ.isGen)
      (DVR.pullGen_isGen _ _ _ _ hσ _)))
  refine ⟨u, hu, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_pull hJ _ _ _).trans ?_)))))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]
end GlobalTheory.DescentPairing
