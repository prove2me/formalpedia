-- Prove2me | solution 1 for GlobalTheory.exists_split_of_coisotropic_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:38.291369+00:00
-- url     : https://prove2.me/submissions/cd28d39f-1619-45ce-8252-a07184220502

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSplitOfCoisotropicKer
import Theorems.Thm_GlobalTheory_KerPerp_exists_isotropic_section
import Theorems.Thm_GlobalTheory_KerPerp_isotropic
import Theorems.Thm_GlobalTheory_KerPerp_mem_kerPerp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O L Y : Type) [CommRing O] [StarRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [Module.Projective O Y] (w : O)
    (EF : LinearMap.BilinForm ℤ L) (y : L →ₗ[O] Y) (hw : w + star w = 1) (halt : ∀ x, EF x x = 0)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module O M) (EM : LinearMap.BilinForm ℤ M) (e : L ≃+ Y × (Y →+ ℤ) × M),
      Function.Bijective EM ∧ (∀ v, (e v).1 = y v) ∧
      (∀ (a : O) v x, (e (a • v)).2.1 x = (e v).2.1 (star a • x)) ∧
      (∀ (a : O) v, (e (a • v)).2.2 = a • (e v).2.2) ∧
      ∀ v v', EF v v' = (e v').2.1 (e v).1 - (e v).2.1 (e v').1 + EM (e v).2.2 (e v').2.2 := by
  obtain ⟨s, hsy, hsiso⟩ := KerPerp.exists_isotropic_section (EF := EF) (y := y) hw halt hb hadj hy hle
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : KerPerp.kerPerp hadj y ≤ LinearMap.ker y := fun t ht =>
    hle t (KerPerp.mem_kerPerp.1 ht)
  obtain ⟨E, hE⟩ : ∃ E : KerPerp.kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y,
      ∀ (t : KerPerp.kerPerp hadj y) (v : L), E t (y v) = -EF t v :=
    ⟨KerPerp.equivDual hadj hb hy, KerPerp.equivDual_apply hadj hb hy⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : L →ₗ[ℤ] Module.Dual ℤ Y, ∀ v x, Φ v x = -EF v (s x) :=
    ⟨-(EF.compl₂ s.toAddMonoidHom.toIntLinearMap), fun _ _ => rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : L →ₗ[ℤ] L, ∀ v, T v = ((E.symm (Φ v) : KerPerp.kerPerp hadj y) : L) :=
    ⟨(KerPerp.kerPerp hadj y).subtype.toAddMonoidHom.toIntLinearMap ∘ₗ E.symm.toLinearMap ∘ₗ Φ,
      fun _ => rfl⟩
  have hTK : ∀ v, T v ∈ KerPerp.kerPerp hadj y := fun v => by rw [hTdef]; exact (E.symm (Φ v)).2
  have hEF : ∀ (t : KerPerp.kerPerp hadj y) w, EF t w = -E t (y w) := fun t w => by rw [hE]; ring
  have hT : ∀ v w, EF (T v) w = EF v (s (y w)) := fun v w => by
    rw [hTdef, hEF, LinearEquiv.apply_symm_apply, hΦ, neg_neg]
  have hTy : ∀ v, y (T v) = 0 := fun v => LinearMap.mem_ker.1 (hle' (hTK v))
  obtain ⟨P, hP⟩ : ∃ P : L →ₗ[ℤ] L, ∀ v, P v = v - s (y v) - T v :=
    ⟨LinearMap.id - s.toAddMonoidHom.toIntLinearMap ∘ₗ y.toAddMonoidHom.toIntLinearMap - T,
      fun _ => rfl⟩
  have hPy : ∀ v, y (P v) = 0 := fun v => by
    rw [hP, map_sub, map_sub, hsy, hTy, sub_self, sub_zero]
  have hPs : ∀ v x, EF (P v) (s x) = 0 := fun v x => by
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsiso, hT, hsy]
    ring
  obtain ⟨N, hN⟩ : ∃ N : Submodule O L, ∀ v, v ∈ N ↔ y v = 0 ∧ ∀ x, EF v (s x) = 0 :=
    ⟨{ carrier := {v | y v = 0 ∧ ∀ x, EF v (s x) = 0}
       add_mem' := fun {a b} ha hb => ⟨by rw [map_add, ha.1, hb.1, add_zero],
         fun x => by rw [map_add, LinearMap.add_apply, ha.2, hb.2, add_zero]⟩
       zero_mem' := ⟨map_zero y, fun x => by rw [map_zero, LinearMap.zero_apply]⟩
       smul_mem' := fun c v hv => ⟨by rw [map_smul, hv.1, smul_zero],
         fun x => by rw [hadj, ← map_smul s, hv.2]⟩ }, fun _ => Iff.rfl⟩
  have hPN : ∀ v, P v ∈ N := fun v => (hN _).2 ⟨hPy v, hPs v⟩
  have hΦN : ∀ m ∈ N, Φ m = 0 := fun m hm => LinearMap.ext fun x => by
    rw [hΦ, ((hN m).1 hm).2, neg_zero, LinearMap.zero_apply]
  have hPfix : ∀ m ∈ N, P m = m := fun m hm => by
    simp [hP, ((hN m).1 hm).1, hTdef, hΦN m hm]
  have hTsmul : ∀ (a : O) v, T (a • v) = a • T v := fun a v => hb.1 (LinearMap.ext fun w => by
    rw [hT, hadj, hadj, hT, map_smul y, map_smul s])
  have hdec : ∀ v, v = s (y v) + T v + P v := fun v => by rw [hP]; abel
  have hback : ∀ φ : Module.Dual ℤ Y, φ.toAddMonoidHom.toIntLinearMap = φ :=
    fun φ => LinearMap.ext fun _ => rfl
  let e : L ≃+ Y × (Y →+ ℤ) × N :=
    { toFun := fun v => (y v, (Φ v).toAddMonoidHom, ⟨P v, hPN v⟩)
      invFun := fun p => s p.1 + ((E.symm p.2.1.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
        (p.2.2 : L)
      left_inv := fun v => by
        show s (y v) + ((E.symm (Φ v).toAddMonoidHom.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
          P v = v
        rw [hback, ← hTdef]
        exact (hdec v).symm
      right_inv := fun p => by
        obtain ⟨a, φ, m⟩ := p
        have hyt : y ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) = 0 :=
          LinearMap.mem_ker.1 (hle' (E.symm _).2)
        have hym : y (m : L) = 0 := ((hN m).1 m.2).1
        have hyv : y (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) = a := by
          rw [map_add, map_add, hsy, hyt, hym, add_zero, add_zero]
        have hΦv : Φ (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) =
            φ.toIntLinearMap := by
          refine LinearMap.ext fun x => ?_
          rw [hΦ, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hsiso, hEF, hsy,
            LinearEquiv.apply_symm_apply, ((hN m).1 m.2).2]
          simp
        refine Prod.ext hyv (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ _ x = φ x
          rw [hΦv]
          rfl
        · show P _ = m
          rw [hP, hyv, hTdef, hΦv]
          exact (fun p q r : L => show p + q + r - p - q = r by abel) _ _ _
      map_add' := fun a b => by
        refine Prod.ext (map_add y a b) (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ (a + b) x = Φ a x + Φ b x
          rw [map_add, LinearMap.add_apply]
        · show P (a + b) = P a + P b
          exact map_add P a b }
  refine ⟨N, inferInstance, inferInstance,
    EF.compl₁₂ N.subtype.toAddMonoidHom.toIntLinearMap N.subtype.toAddMonoidHom.toIntLinearMap, e,
    ⟨?_, ?_⟩, fun v => rfl, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    apply Subtype.ext
    apply hb.1
    refine LinearMap.ext fun w => ?_
    have hm' : EF (m : L) (P w) = 0 := by
      simpa using LinearMap.congr_fun hm ⟨P w, hPN w⟩
    have hmN := (hN m).1 m.2
    rw [Submodule.coe_zero, map_zero, LinearMap.zero_apply, hdec w, map_add, map_add, hmN.2, hm',
      skew, hT, hmN.1, map_zero, map_zero]
    simp
  · intro g
    obtain ⟨v, hv⟩ := hb.2 (g ∘ₗ (AddMonoidHom.mk' (fun v => (⟨P v, hPN v⟩ : N))
      (fun a b => Subtype.ext (map_add P a b))).toIntLinearMap)
    refine ⟨⟨P v, hPN v⟩, LinearMap.ext fun m => ?_⟩
    have h1 : EF v m = g ⟨P m, hPN m⟩ := LinearMap.congr_fun hv m
    have h2 : (⟨P m, hPN m⟩ : N) = m := Subtype.ext (hPfix m m.2)
    have hmN := (hN m).1 m.2
    show EF (P v) m = g m
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [h1, h2, skew (s (y v)), hmN.2, hT, hmN.1, map_zero, map_zero]
    simp
  · intro a v x
    show Φ (a • v) x = Φ v (star a • x)
    rw [hΦ, hΦ, hadj, map_smul s]
  · intro a v
    refine Subtype.ext ?_
    show P (a • v) = a • P v
    rw [hP, hP, map_smul y, map_smul s, hTsmul, smul_sub, smul_sub]
  · intro v v'
    show EF v v' = Φ v' (y v) - Φ v (y v') + EF (P v) (P v')
    rw [hΦ, hΦ, hP, hP]
    simp only [map_sub, LinearMap.sub_apply]
    have f1 := hT v v'
    have f2 := hT v (s (y v'))
    rw [hsy] at f2
    have f3 : EF v (T v') = -EF v' (s (y v)) := by rw [skew, hT]
    have f4 : EF (s (y v)) (T v') = -EF v' (s (y (s (y v)))) := by rw [skew, hT]
    rw [hsy] at f4
    have f5 := hsiso (y v) (y v')
    have f6 : EF (T v) (T v') = 0 := KerPerp.isotropic hle' (hTK v) (hTK v')
    have f7 := skew (s (y v)) v'
    linarith
end GlobalTheory
