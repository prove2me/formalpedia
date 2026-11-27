-- Prove2me | solution 1 for GlobalTheory.ZM.EmbedLocal.of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:34.561224+00:00
-- url     : https://prove2.me/submissions/1f54e8fa-e828-41ac-9010-84ca3785f8ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalMultiplicationPullbackThetaEmbeddingI
import Theorems.Thm_GlobalTheory_ZM_EmbedLocal_isPullback_whisker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.EmbedLocal
namespace GlobalTheory.ZM.EmbedLocal
theorem _root_.solution
    (hex : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ)
    (hpb : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T T' : Over S) (h : T' ⟶ T) σ, IsAffine T.left → IsAffine T'.left → t.Emb m T σ → ∃ σ', t.Emb m T' σ' ∧ ∀ (R : Type) [CommRing R] (y : Sp R ⟶ (T' ⊗ t.A).left) (w : Ix g (N' ^ 2) → R), SecCoord _ σ' y w ↔ SecCoord _ σ (y ≫ (h ▷ t.A).left) w)
    (hspan : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤)
    (hva : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ)
    (hfib : ∀ (R σ : Type) [CommRing R] [Finite σ] (X : Scheme.{0}) (s : X ⟶ Sp R) (M : LB X) (th : σ → M.Sec), M.IsLB → IsProper s → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K), ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (s' : X' ⟶ Sp K) (M' : LB X') (th' : σ → M'.Sec) (I : Ideal (MvPolynomial σ K)), IsPullback π s' s (spMap x) ∧ ProjRep I s' M' th' ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X') (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ π) w) → ProjRep (idealOf s M th (𝟙 X)) s M th) :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ := by
  intro l1 l2 o _ g N' J b S s t m R _ x v hm h2 hth p
  have hodd : Odd N' := hth.1
  have hdvd : m ∣ N' := (dvd_pow_self m two_ne_zero).trans hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hodd.pos.ne'⟩
  obtain ⟨R', _, φ, σ, hφ, hp, hE⟩ := hex l1 l2 o g N' J b S s t m R x hodd hdvd p
  refine ⟨R', inferInstance, φ, σ, hφ, hp, hE, ?_⟩
  refine hfib R' (Ix g (N' ^ 2)) _ _ _ σ (LB.isLB_linComb t.isLB _ _) ?_ ?_
  · haveI := t.ab.proper
    exact inferInstanceAs (IsProper (pullback.fst (spMap φ ≫ x) t.A.hom))
  · intro K _ _ y
    let h : Over.mk (spMap y ≫ spMap φ ≫ x) ⟶ Over.mk (spMap φ ≫ x) := Over.homMk (spMap y) rfl
    obtain ⟨σ', hE', hc⟩ := hpb l2 o g N' J b S s t m _ _ h σ
      (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) hE
    have hs := hspan l1 l2 o g N' J b S s t m K _ σ' hodd hdvd h2 hE'
    have h4 : (4 : ℤ) ≤ (m : ℤ) ^ 2 := by
      have : (2 : ℤ) ≤ m := by exact_mod_cast h2
      nlinarith
    exact ⟨_, (h ▷ t.A).left, _, _, σ', _, isPullback_whisker t.A h,
      hva l1 l2 S t.pol K _ _ _ σ' h4 hs, hc⟩
end GlobalTheory.ZM.EmbedLocal
