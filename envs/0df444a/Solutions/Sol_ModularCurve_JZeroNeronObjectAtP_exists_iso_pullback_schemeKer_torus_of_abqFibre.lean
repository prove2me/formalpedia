-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_iso_pullback_schemeKer_torus_of_abqFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d870e119-e636-5897-9e17-3e7c8ab0495c

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

universe u

noncomputable section

namespace TorsorIso

section KerPts

variable {S : Type u} [CommRing S] {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of S)}
  (H : RelativeGroupLaw S h) (n : ℕ)

theorem comp_schemeNsmul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (z : SchemeHomOver t h) :
    z.1 ≫ H.schemeNsmul n = (H.nsmul t n z).1 := by
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (RelativeGroupLaw.idPoint (f := h)) = z :=
    Subtype.ext (Category.comp_id _)
  have key := congrArg Subtype.val (H.nsmul_natural h t z.1 z.2 n RelativeGroupLaw.idPoint)
  rw [e, GoodReductionJacobian.schemeHomOverComp_coe] at key
  exact key

theorem schemeKer_fst_comp {T : Scheme.{u}} (a : T ⟶ H.schemeKer n) :
    (a ≫ pullback.fst _ _) ≫ h = a ≫ H.schemeKerStr n := by
  calc (a ≫ pullback.fst _ _) ≫ h
      = a ≫ pullback.fst _ _ ≫ (H.schemeNsmul n ≫ h) := by rw [H.schemeNsmul_over, Category.assoc]
    _ = a ≫ (pullback.fst _ _ ≫ H.schemeNsmul n) ≫ h := by simp only [Category.assoc]
    _ = a ≫ (pullback.snd _ _ ≫ (H.one (𝟙 _)).1) ≫ h := by rw [pullback.condition]
    _ = a ≫ H.schemeKerStr n := by rw [Category.assoc, (H.one (𝟙 _)).2, Category.comp_id]

def kerPtOut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : SchemeHomOver t h :=
  ⟨a ≫ pullback.fst _ _, (schemeKer_fst_comp H n a).trans ha⟩

@[scoped simp]
theorem kerPtOut_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : (kerPtOut H n t a ha).1 = a ≫ pullback.fst _ _ :=
  rfl

theorem nsmul_kerPtOut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : H.nsmul t n (kerPtOut H n t a ha) = H.one t := by
  apply Subtype.ext
  rw [← comp_schemeNsmul, RelativeGroupLaw.one_coe_eq, kerPtOut_coe, ← ha]
  simp only [Category.assoc, pullback.condition]

def kerPtIn {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : T ⟶ H.schemeKer n :=
  pullback.lift z.1 t (by rw [comp_schemeNsmul, hz, RelativeGroupLaw.one_coe_eq])

@[scoped simp]
theorem kerPtIn_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : kerPtIn H n t z hz ≫ pullback.fst _ _ = z.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem kerPtIn_str {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : kerPtIn H n t z hz ≫ H.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

theorem schemeKer_hom_ext {T : Scheme.{u}} {a b : T ⟶ H.schemeKer n}
    (h1 : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _) : a = b := by
  apply pullback.hom_ext h1
  change a ≫ H.schemeKerStr n = b ≫ H.schemeKerStr n
  rw [← schemeKer_fst_comp, ← schemeKer_fst_comp, h1]

end KerPts

section Alg

variable {S : Type u} [CommRing S] {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of S)} (H : RelativeGroupLaw S h)
  {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of S))

theorem nsmul_mul (hc : H.IsCommutative) (n : ℕ) (x y : SchemeHomOver w h) :
    H.nsmul w n (H.mul w x y) = H.mul w (H.nsmul w n x) (H.nsmul w n y) := by
  induction n with
  | zero => simp only [RelativeGroupLaw.nsmul_zero]; exact (H.one_mul w _).symm
  | succ n ih =>
    simp only [RelativeGroupLaw.nsmul_succ, ih]
    rw [H.mul_assoc w (H.nsmul w n x) (H.nsmul w n y) (H.mul w x y),
      H.mul_assoc w (H.nsmul w n x) x (H.mul w (H.nsmul w n y) y),
      ← H.mul_assoc w (H.nsmul w n y) x y, hc w (H.nsmul w n y) x, H.mul_assoc w x (H.nsmul w n y) y]

theorem nsmul_inv (hc : H.IsCommutative) (n : ℕ) (x : SchemeHomOver w h) :
    H.nsmul w n (H.inv w x) = H.inv w (H.nsmul w n x) := by
  letI := H.pointGroup w
  have h1 : H.nsmul w n x * H.nsmul w n (H.inv w x) = 1 := by
    show H.mul w _ _ = H.one w
    rw [← nsmul_mul H w hc, H.mul_inv_cancel, RelativeGroupLaw.nsmul_unit]
  exact (eq_inv_of_mul_eq_one_right h1)

theorem inv_natural {W' : Scheme.{u}} (w' : W' ⟶ Spec (CommRingCat.of S)) (ψ : W' ⟶ W) (hψ : ψ ≫ w = w')
    (x : SchemeHomOver w h) :
    schemeHomOverComp ψ hψ (H.inv w x) = H.inv w' (schemeHomOverComp ψ hψ x) := by
  letI := H.pointGroup w'
  have h1 : schemeHomOverComp ψ hψ (H.inv w x) * schemeHomOverComp ψ hψ x = 1 := by
    show H.mul w' _ _ = H.one w'
    rw [← H.mul_natural w w' ψ hψ, H.inv_mul_cancel, H.one_natural w w' ψ hψ]
  exact eq_inv_of_mul_eq_one_left h1

end Alg

end TorsorIso
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre.TorsorIso"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre.TorsorIso"

open TorsorIso in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (ψ : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶
      pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
    (hψ₀ : ψ ≫ pullback.fst _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 0).1)
    (hψ₁ : ψ ≫ pullback.snd _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 1).1) :
    letI KL := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA))
      (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)
    ∃ φ : pullback (KL.schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ≅ pullback ψ ψ,
      φ.hom ≫ pullback.snd ψ ψ = pullback.snd _ _ := by

  haveI := O.separated
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  have hcG : (O.L.baseChange (resPt A ≫ Λ.σA)).IsCommutative := RelativeGroupLaw.IsCommutative.baseChange (resPt A ≫ Λ.σA) O.comm
  have habq : ∀ i, RelativeGroupLaw.IsHom (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (O.abqFibre i) := fun i => O.abqFibre_mul i

  haveI : IsClosedImmersion ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))).1 :=
    RelativeGroupLaw.isClosedImmersion_one (Λ.L.baseChange (resPt A ≫ Λ.σA))
  haveI : IsClosedImmersion ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))).1 :=
    RelativeGroupLaw.isClosedImmersion_one (O.L.baseChange (resPt A ≫ Λ.σA))
  let jG := pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1
  let jA := pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1
  let jK := pullback.fst ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeNsmul m) ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).one (𝟙 _)).1
  let κι := RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre
  haveI : Mono κι := inferInstance
  haveI : Mono jA := pullback.fst_of_mono
  haveI : Mono jG := pullback.fst_of_mono

  have hψ0' : ∀ (T : Scheme.{0}) (z : T ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m),
      z ≫ ψ ≫ pullback.fst _ _ ≫ jA = z ≫ jG ≫ (O.abqFibre 0).1 := by
    intro T z; rw [hψ₀]
  have hψ1' : ∀ (T : Scheme.{0}) (z : T ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m),
      z ≫ ψ ≫ pullback.snd _ _ ≫ jA = z ≫ jG ≫ (O.abqFibre 1).1 := by
    intro T z; rw [hψ₁]

  have hψover : ψ ≫ pullback.fst _ _ ≫ (Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m = (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m := by
    have h1 : jA ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f = (Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m := by
      have := schemeKer_fst_comp (Λ.L.baseChange (resPt A ≫ Λ.σA)) m (𝟙 _)
      simp only [Category.id_comp] at this
      exact this
    have h2 : jG ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g = (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m := by
      have := schemeKer_fst_comp (O.L.baseChange (resPt A ≫ Λ.σA)) m (𝟙 _)
      simp only [Category.id_comp] at this
      exact this
    have h3 := congrArg (· ≫ RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) hψ₀
    simp only [Category.assoc] at h3
    rw [h1, (O.abqFibre 0).2, h2] at h3
    exact h3

  let P := pullback ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
  let t : P ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := pullback.snd ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m
  let x : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := kerPtOut (O.L.baseChange (resPt A ≫ Λ.σA)) m t (pullback.snd _ _) rfl
  let kK : SchemeHomOver t (RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre) :=
    kerPtOut (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)) m t (pullback.fst _ _) pullback.condition
  let kGp := RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre t kK
  let kG : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := kGp.1
  have hkG_tors : (O.L.baseChange (resPt A ≫ Λ.σA)).nsmul t m kG = (O.L.baseChange (resPt A ≫ Λ.σA)).one t := by
    have := RelativeGroupLaw.kerPairPointEquiv_nsmul (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i) t m kK
    rw [nsmul_kerPtOut, RelativeGroupLaw.kerPairPointEquiv_one] at this
    exact this.symm
  have hx_tors : (O.L.baseChange (resPt A ≫ Λ.σA)).nsmul t m x = (O.L.baseChange (resPt A ≫ Λ.σA)).one t := nsmul_kerPtOut (O.L.baseChange (resPt A ≫ Λ.σA)) m t _ rfl
  let w : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := (O.L.baseChange (resPt A ≫ Λ.σA)).mul t kG x
  have hw_tors : (O.L.baseChange (resPt A ≫ Λ.σA)).nsmul t m w = (O.L.baseChange (resPt A ≫ Λ.σA)).one t := by
    rw [nsmul_mul (O.L.baseChange (resPt A ≫ Λ.σA)) t hcG, hkG_tors, hx_tors, (O.L.baseChange (resPt A ≫ Λ.σA)).one_mul]
  have hw_abq : ∀ i, NeronModelInfra.schemeHomOverComp w (O.abqFibre i) = NeronModelInfra.schemeHomOverComp x (O.abqFibre i) := by
    intro i
    show NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).mul t kG x) (O.abqFibre i) = _
    rw [habq i t, kGp.2 i, (Λ.L.baseChange (resPt A ≫ Λ.σA)).one_mul]
  let wIn : P ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m := kerPtIn (O.L.baseChange (resPt A ≫ Λ.σA)) m t w hw_tors
  have hφcond : wIn ≫ ψ = pullback.snd ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ≫ ψ := by
    apply pullback.hom_ext
    · rw [← cancel_mono jA, Category.assoc, Category.assoc, Category.assoc, Category.assoc]
      rw [hψ0' _ wIn, hψ0' _ (pullback.snd ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)), ← Category.assoc wIn, kerPtIn_fst]
      exact congrArg Subtype.val (hw_abq 0)
    · rw [← cancel_mono jA, Category.assoc, Category.assoc, Category.assoc, Category.assoc]
      rw [hψ1' _ wIn, hψ1' _ (pullback.snd ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)), ← Category.assoc wIn, kerPtIn_fst]
      exact congrArg Subtype.val (hw_abq 1)
  let φhom : P ⟶ pullback ψ ψ := pullback.lift wIn (pullback.snd _ _) hφcond

  let Q := pullback ψ ψ
  let a := pullback.fst ψ ψ
  let b := pullback.snd ψ ψ
  let t' : Q ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := b ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m
  have hat' : a ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m = t' := by
    show a ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m = b ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m
    rw [← hψover, ← Category.assoc, pullback.condition, Category.assoc]
  let xa := kerPtOut (O.L.baseChange (resPt A ≫ Λ.σA)) m t' a hat'
  let xb := kerPtOut (O.L.baseChange (resPt A ≫ Λ.σA)) m t' b rfl
  have hxab : ∀ i, NeronModelInfra.schemeHomOverComp xa (O.abqFibre i) = NeronModelInfra.schemeHomOverComp xb (O.abqFibre i) := by
    intro i
    apply Subtype.ext
    show (a ≫ jG) ≫ (O.abqFibre i).1 = (b ≫ jG) ≫ (O.abqFibre i).1
    fin_cases i
    · show (a ≫ jG) ≫ (O.abqFibre 0).1 = (b ≫ jG) ≫ (O.abqFibre 0).1
      rw [Category.assoc, Category.assoc, ← hψ0' _ a, ← hψ0' _ b, ← Category.assoc, pullback.condition, Category.assoc]
    · show (a ≫ jG) ≫ (O.abqFibre 1).1 = (b ≫ jG) ≫ (O.abqFibre 1).1
      rw [Category.assoc, Category.assoc, ← hψ1' _ a, ← hψ1' _ b, ← Category.assoc, pullback.condition, Category.assoc]
  let q : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) := (O.L.baseChange (resPt A ≫ Λ.σA)).mul t' xa ((O.L.baseChange (resPt A ≫ Λ.σA)).inv t' xb)
  have hq_ker : ∀ i, NeronModelInfra.schemeHomOverComp q (O.abqFibre i) = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one t' := by
    intro i
    show NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).mul t' xa ((O.L.baseChange (resPt A ≫ Λ.σA)).inv t' xb)) (O.abqFibre i) = _
    rw [habq i t', RelativeGroupLaw.IsHom.inv (habq i) t', hxab i, (Λ.L.baseChange (resPt A ≫ Λ.σA)).mul_inv_cancel]
  let qK : SchemeHomOver t' (RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre) :=
    (RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre t').symm ⟨q, hq_ker⟩
  have hq_tors : (O.L.baseChange (resPt A ≫ Λ.σA)).nsmul t' m q = (O.L.baseChange (resPt A ≫ Λ.σA)).one t' := by
    show (O.L.baseChange (resPt A ≫ Λ.σA)).nsmul t' m ((O.L.baseChange (resPt A ≫ Λ.σA)).mul t' xa ((O.L.baseChange (resPt A ≫ Λ.σA)).inv t' xb)) = _
    rw [nsmul_mul (O.L.baseChange (resPt A ≫ Λ.σA)) t' hcG, nsmul_inv (O.L.baseChange (resPt A ≫ Λ.σA)) t' hcG, nsmul_kerPtOut, nsmul_kerPtOut, (O.L.baseChange (resPt A ≫ Λ.σA)).mul_inv_cancel]
  have hqK_tors : (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).nsmul t' m qK = (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).one t' := by
    apply (RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre t').injective
    apply Subtype.ext
    rw [RelativeGroupLaw.kerPairPointEquiv_nsmul, RelativeGroupLaw.kerPairPointEquiv_one]
    show (O.L.baseChange (resPt A ≫ Λ.σA)).nsmul t' m (RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre t' ((RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre t').symm ⟨q, hq_ker⟩)).1 = _
    rw [Equiv.apply_symm_apply]
    exact hq_tors
  let qIn : Q ⟶ (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeKer m := kerPtIn (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)) m t' qK hqK_tors
  let φinv : Q ⟶ P := pullback.lift qIn b (by rw [kerPtIn_str])

  have hqK1 : qK.1 ≫ κι = q.1 := RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe _ _ _ _
  have hkG1 : kG.1 = pullback.fst _ _ ≫ jK ≫ κι := Category.assoc _ _ _

  have hφt : φhom ≫ t' = t := by
    show φhom ≫ b ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m = pullback.snd _ _ ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m
    rw [← Category.assoc, pullback.lift_snd]
  have hφ't : φinv ≫ t = t' := by
    show φinv ≫ pullback.snd _ _ ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m = b ≫ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m
    rw [← Category.assoc, pullback.lift_snd]
  have hom_inv : φhom ≫ φinv = 𝟙 P := by
    apply pullback.hom_ext
    ·
      rw [Category.id_comp, Category.assoc, pullback.lift_fst]
      apply schemeKer_hom_ext (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)) m
      rw [Category.assoc, kerPtIn_fst]
      rw [← cancel_mono κι, Category.assoc, hqK1, Category.assoc]

      have hxa : schemeHomOverComp φhom hφt xa = w := by
        apply Subtype.ext
        show φhom ≫ a ≫ jG = w.1
        rw [← Category.assoc, pullback.lift_fst, kerPtIn_fst]
      have hxb : schemeHomOverComp φhom hφt xb = x := by
        apply Subtype.ext
        show φhom ≫ b ≫ jG = (pullback.snd _ _) ≫ jG
        rw [← Category.assoc, pullback.lift_snd]
      have : schemeHomOverComp φhom hφt q = kG := by
        show schemeHomOverComp φhom hφt ((O.L.baseChange (resPt A ≫ Λ.σA)).mul t' xa ((O.L.baseChange (resPt A ≫ Λ.σA)).inv t' xb)) = kG
        rw [(O.L.baseChange (resPt A ≫ Λ.σA)).mul_natural t' t φhom hφt, inv_natural (O.L.baseChange (resPt A ≫ Λ.σA)) t' t φhom hφt, hxa, hxb]
        show (O.L.baseChange (resPt A ≫ Λ.σA)).mul t ((O.L.baseChange (resPt A ≫ Λ.σA)).mul t kG x) ((O.L.baseChange (resPt A ≫ Λ.σA)).inv t x) = kG
        rw [(O.L.baseChange (resPt A ≫ Λ.σA)).mul_assoc, (O.L.baseChange (resPt A ≫ Λ.σA)).mul_inv_cancel, (O.L.baseChange (resPt A ≫ Λ.σA)).mul_one]
      exact (congrArg Subtype.val this).trans hkG1
    · rw [Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have inv_hom : φinv ≫ φhom = 𝟙 Q := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst]
      apply schemeKer_hom_ext (O.L.baseChange (resPt A ≫ Λ.σA)) m
      rw [Category.assoc, kerPtIn_fst]

      have hx' : schemeHomOverComp φinv hφ't x = xb := by
        apply Subtype.ext
        show φinv ≫ (pullback.snd _ _) ≫ jG = b ≫ jG
        rw [← Category.assoc, pullback.lift_snd]
      have hk' : schemeHomOverComp φinv hφ't kG = q := by
        apply Subtype.ext
        have e1 : φinv ≫ pullback.fst _ _ = qIn := pullback.lift_fst _ _ _
        have e2 : qIn ≫ jK = qK.1 := kerPtIn_fst _ _ _ _ _
        change φinv ≫ (pullback.fst _ _ ≫ jK) ≫ κι = q.1
        rw [← hqK1, ← e2, ← e1]
        simp only [Category.assoc]
      have : schemeHomOverComp φinv hφ't w = xa := by
        show schemeHomOverComp φinv hφ't ((O.L.baseChange (resPt A ≫ Λ.σA)).mul t kG x) = xa
        rw [(O.L.baseChange (resPt A ≫ Λ.σA)).mul_natural t t' φinv hφ't, hk', hx']
        show (O.L.baseChange (resPt A ≫ Λ.σA)).mul t' ((O.L.baseChange (resPt A ≫ Λ.σA)).mul t' xa ((O.L.baseChange (resPt A ≫ Λ.σA)).inv t' xb)) xb = xa
        rw [(O.L.baseChange (resPt A ≫ Λ.σA)).mul_assoc, (O.L.baseChange (resPt A ≫ Λ.σA)).inv_mul_cancel, (O.L.baseChange (resPt A ≫ Λ.σA)).mul_one]
      exact congrArg Subtype.val this
    · rw [Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  exact ⟨⟨φhom, φinv, hom_inv, inv_hom⟩, pullback.lift_snd _ _ _⟩

end S_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre (solution)
