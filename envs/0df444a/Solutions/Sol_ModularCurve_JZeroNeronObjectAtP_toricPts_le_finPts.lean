-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.toricPts_le_finPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b14f9034-a948-5829-b9ab-7f9a910bd456

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_le_finPts

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_le_finPts.ModularCurve ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_le_finPts.ModularCurve.JZeroNeronObjectAtP"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP JZeroNeronData JZero"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base barPt muCoord muStr castOver genOfBaseChangePt ExtendsToPlace LevelData toricPoint toricPts finPts toricLift_mul toricLift L G pts_add comp g toricRank pts"
namespace ToricLeFin
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

section conv

variable {S : Type} [CommRing S] {L : Type} [CommRing L] [Algebra S L] {G : Type} [AddMonoid G]

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) :
    (c * c') (AddMonoidAlgebra.single v 1) =
      c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G) :
    (1 : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) (n : ℕ) :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, convMul_apply_single, ih, pow_succ]

theorem conv_ext {c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)}
    (h : ∀ v, c (AddMonoidAlgebra.single v 1) = c' (AddMonoidAlgebra.single v 1)) : c = c' := by
  have : c.ofConv = c'.ofConv := AddMonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)
  exact congrArg WithConv.toConv this

theorem convPow_eq_one (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (n : ℕ) (hn : ∀ v : G, n • v = 0) :
    c ^ n = 1 := by
  refine conv_ext (fun v => ?_)
  rw [convPow_apply_single, convOne_apply_single, ← map_pow, AddMonoidAlgebra.single_pow, hn, one_pow]
  exact map_one c.ofConv

end conv

theorem castOver_mul {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (x y : SchemeHomOver ι f) :
    castOver h (L.mul ι x y) = L.mul ι' (castOver h x) (castOver h y) := by
  subst h; rfl

section toric

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
  (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

theorem genOfBaseChangePt_mul
    (y y' : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :
    genOfBaseChangePt Λ.hσA ((O.L.baseChange Λ.σA).mul _ y y') =
      O.L.mul _ (genOfBaseChangePt Λ.hσA y) (genOfBaseChangePt Λ.hσA y') := by
  unfold genOfBaseChangePt
  rw [RelativeGroupLaw.baseChangePointToBase_mul]
  exact castOver_mul O.L Λ.hσA _ _

theorem toricPoint_mul {m : ℕ} (hm : 0 < m)
    (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) :
    O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv := by
  apply O.pts.injective
  rw [O.pts_add]
  unfold toricPoint
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, O.toricLift_mul m hm χ χ',
    genOfBaseChangePt_mul]

def toricPointHom {m : ℕ} (hm : 0 < m) :
    WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) →* Multiplicative (JZero (N₀ * p)) where
  toFun χ := Multiplicative.ofAdd (O.toricPoint m hm χ.ofConv)
  map_one' := by
    have h := toricPoint_mul O hm 1 1
    rw [mul_one] at h
    have h0 : O.toricPoint m hm
        (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
      have := congrArg (fun z => z - O.toricPoint m hm
        (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv) h
      simpa using this.symm
    rw [h0]; rfl
  map_mul' χ χ' := by rw [← ofAdd_add, ← toricPoint_mul]

theorem nsmul_toricPoint_eq_zero {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    m • O.toricPoint m hm χ = 0 := by
  have h := (toricPointHom O hm).map_pow (WithConv.toConv χ) m
  rw [convPow_eq_one _ m (fun v => ?_), map_one] at h
  ·
    have h' := congrArg Multiplicative.toAdd h
    simpa [toricPointHom] using h'.symm
  ·
    funext i; simp

theorem extendsToPlace_toricPoint {m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    ExtendsToPlace A Λ.σA (O.pts (O.toricPoint m hm χ)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨-, χA, hχA⟩ := ValuationSubring.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder A
    (fun v : Fin O.toricRank → ZMod m => isOfFinAddOrder_of_finite v) χ

  have hfac : χ.toRingHom = A.subtype.comp χA.toRingHom :=
    RingHom.ext (fun z => (hχA z).symm)

  let ι := O.toricLift m hm
  have hsec : Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ muStr ↥A O.toricRank m = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χA.toRingHom.comp (algebraMap ↥A (muCoord ↥A O.toricRank m)) = RingHom.id ↥A := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  refine ⟨⟨Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ ι.1 ≫ pullback.fst O.g Λ.σA, ?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc ι.1, ι.2, ← Category.assoc, hsec,
      Category.id_comp]
  ·
    unfold toricPoint
    rw [Equiv.apply_symm_apply]
    change (RelativeGroupLaw.baseChangePointToBase Λ.σA _).1 = _
    rw [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe]
    change (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ ι.1) ≫ _ = _
    rw [hfac, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc]

end toric

end ModularCurve.JZeroNeronObjectAtP.ToricLeFin

end

open ModularCurve.JZeroNeronObjectAtP.ToricLeFin in

theorem solution
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) : O.toricPts m ≤ O.finPts m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [toricPts, dif_neg (lt_irrefl 0)]
    exact bot_le
  rw [toricPts, dif_pos hm, AddSubgroup.closure_le]
  rintro _ ⟨χ, rfl⟩
  apply AddSubgroup.subset_closure
  refine ⟨?_, extendsToPlace_toricPoint O hm χ⟩

  change O.toricPoint m hm χ ∈ (Submodule.torsionBy ℤ (JZero (N₀ * p)) (m : ℤ)).toAddSubgroup
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul]
  exact nsmul_toricPoint_eq_zero O hm χ

end S_ModularCurve_JZeroNeronObjectAtP_toricPts_le_finPts
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPts_le_finPts (solution)
