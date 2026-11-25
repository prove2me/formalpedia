-- Prove2me | solution 1 for GlobalTheory.DescentPairing.exists_gen_transl_eq_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:19.075001+00:00
-- url     : https://prove2.me/submissions/7e0d90e1-2d5b-4cf8-9e7b-d2bd46cdc982

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
import Theorems.Thm_GlobalTheory_DescentPairing_cubN_transl
import Theorems.Thm_GlobalTheory_DescentPairing_exists_theta
import Theorems.Thm_GlobalTheory_DescentPairing_exists_triv
import Theorems.Thm_GlobalTheory_CommutatorPairing_commIsOf_iff
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translT
import Theorems.Thm_GlobalTheory_CommutatorPairing_val_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
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
theorem _root_.solution : GlobalFnsSt → CubeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → WeilSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε))) := by
  intro _ hC hW _ K _ _ P n x hx
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let p₀ : (baseOver (Spec (CommRingCat.of K))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hT : ∀ p : (baseOver (Spec (CommRingCat.of K))).left, p = p₀ := fun p =>
    Subsingleton.elim (α := PrimeSpectrum K) p p₀
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, 1, hu, Or.inl rfl, fun y c hy hc => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff P.isLB θx θy c).1 (((hW _ P n _).1 θx θy c).1 hc)
  refine corr_of_val P.isLB fun z J hJ => ?_
  have e : 𝟙 (baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left = (lift (fst _ P.A) (snd _ P.A)).left := by
    rw [lift_fst_snd]; rfl
  rw [e]
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg (_ * ·) (val_const (c ^ (1 : ℤ)) _ _ z J))).symm)
  rw [← Over.comp_left, lift_translT, zpow_one]
  obtain ⟨s, hs⟩ := vu _ (fst _ P.A) z J hJ
  obtain ⟨s', hs'⟩ := vy _ (fst _ P.A) z J hJ
  have k₁ := hcm _ (fst _ P.A) (snd _ P.A) z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (fst _ P.A ≫ θy.pt) (snd _ P.A) (fst _ P.A ≫ θx.pt)
    ((map_pow (preHom (fst _ P.A)) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' (snd _ P.A)
  have t₂ := hs' ((fst _ P.A ≫ θx.pt) * snd _ P.A)
  apply Additive.ofMul.injective
  have E := fun {p q : ((baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left.presheaf.stalk z)ˣ} (e : p = q) =>
    congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂
end GlobalTheory.DescentPairing
