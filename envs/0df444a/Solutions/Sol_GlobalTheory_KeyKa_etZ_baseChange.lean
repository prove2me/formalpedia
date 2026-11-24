-- Prove2me | solution 1 for GlobalTheory.KeyKa.etZ_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:48.219045+00:00
-- url     : https://prove2.me/submissions/9f2dc64b-522f-4924-85b5-245e79f8c6b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_eq
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_spMap
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_snd_map
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_snd_pow_mul
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_translate_le
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_fst_valT_translate
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_translate_comp
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_le_inf_pull
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_via
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_mem_nonzeroLocus_via
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa
open EtBaseChange
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → EtZ x s z ch → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → R'ˣ), EtZ x' s' z' ch' ∧ (∀ a, jac x' s' (z' a) (ch' a) * (u a : R') ^ (x.P.g * n) = f (jac x s (z a) (ch a))) ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := R') (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : R') ^ l = f (valT (T := R) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  intro R R' _ _ _ _ x x' f φ w n d hg s s' z ch ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩
  have hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f := fun a =>
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Fin d → Pt x' := fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)
  have hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left := fun a => hp.1.lift_fst _ _ _
  have hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint R'))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open
      (x'.P.L.U i).isOpen hi⟩
  choose ch' hch' using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := R') (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → R'ˣ := fun a => Units.map (valH (T := R') (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := R') (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg →
      valT (T := R') (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : R') ^ l =
        f (valT (T := R) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by
    have e := valT_via (T := R') h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := R') q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)
  have hzero : ∀ a i, valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval n _ _ a (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : R') ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z a) * x.v (k.cast hg)).left
        (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : R') ^ n * TrivSqZeroExt.snd (valT (T := DualNumber R')
          ((toUnit (epsR R') ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR R') ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber R') (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber R') q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : R') ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hjac, hval⟩
  · exact isUnit_of_mul_isUnit_left (hjac a ▸ (hz₃ a).map f)
  · refine hz₄ a a' h (spMap f p) ?_
    have e₁ := congrArg (fun q => q p) (hz' a)
    have e₂ := congrArg (fun q => q p) (hz' a')
    exact e₁.symm.trans ((congrArg φ e).trans e₂)
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp R')) (f := 𝟙 (Sp R)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩
end GlobalTheory.KeyKa
