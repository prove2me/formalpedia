-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/edda0939-ee58-5319-a8ab-7d7ac603ccf0

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_bialgHom_apply_eq_algebraMap_counit_of_etale_cartierDual_of_sub_mem_map_maximalIdeal
import Theorems.Thm_CartierDual_algebraEtale_addMonoidAlgebra
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point
import Theorems.Thm_BialgHom_exists_coe_eq_of_forall_withConv_comp
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeKerStr_of_locallyQuasiFinite_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

universe u

namespace C2Rigid

theorem aux_isReduced_baseChange_tensor_addMonoidAlgebra {A : Type} [CommRing A] (K : Type) [Field K] [CharZero K]
    [Algebra A K] (G : Type) [AddCommGroup G] [Finite G] :
    IsReduced (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G)) := by
  haveI : Module.Finite K (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G)) := inferInstance
  haveI : Algebra.FiniteType K (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G)) := Module.Finite.finiteType _
  exact HopfAlgebra.isReduced_of_finiteType_of_charZero K (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G))

theorem aux_noZeroSMulDivisors_of_free {A : Type} [CommRing A] [IsDomain A] (M : Type) [AddCommGroup M] [Module A M]
    [Module.Free A M] : NoZeroSMulDivisors A M := by
  classical
  refine ⟨fun {c x} h => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    apply (Module.Free.chooseBasis A M).repr.injective
    rw [map_zero]
    ext j
    have hj := congrArg (fun y => (Module.Free.chooseBasis A M).repr y j) h
    simp only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.zero_apply, smul_eq_mul] at hj
    exact (mul_eq_zero.mp hj).resolve_left hc

theorem inv_natural {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  exact inv_eq_of_mul_eq_one_left h |>.symm

theorem eq_one_of_mul_self {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

theorem mem_map_of_forall_apply_mem {S : Type} [CommRing S] (I : Ideal S) {M : Type} [AddCommMonoid M]
    (x : AddMonoidAlgebra S M) (hx : ∀ j : M, x.coeff j ∈ I) :
    x ∈ I.map (algebraMap S (AddMonoidAlgebra S M)) := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  have : (AddMonoidAlgebra.single j (x.coeff j) : AddMonoidAlgebra S M) =
      algebraMap S (AddMonoidAlgebra S M) (x.coeff j) * AddMonoidAlgebra.single j 1 := by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hx j))

end C2Rigid

open C2Rigid in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (u v : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hu : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) u =
        (O.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) u)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) u))
    (hv : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) v =
        (O.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) v)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) v))
    (huv : muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ u.1 =
      muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ v.1) :
    u = v := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩

  haveI : IsSeparated O.g := O.separated
  haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA O.g) := by
    show IsSeparated (pullback.snd O.g Λ.σA); infer_instance
  haveI : LocallyOfFiniteType (RelativeGroupLaw.baseChangeStr Λ.σA O.g) := by
    show LocallyOfFiniteType (pullback.snd O.g Λ.σA); infer_instance
  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  set LA := O.L.baseChange Λ.σA with hLA
  have hcommA : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A))
      (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr Λ.σA O.g)), LA.mul t x y = LA.mul t y x :=
    fun t x y => RelativeGroupLaw.IsCommutative.baseChange (ι := Λ.σA) (G := O.L) O.comm t x y

  have hcomp : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of ↥A)} (x : SchemeHomOver s (muStr ↥A O.toricRank m))
      (w : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp x w = GoodReductionJacobian.schemeHomOverComp x.1 x.2 w := by
    intro T s x w; rfl

  obtain ⟨w, hw⟩ : ∃ w : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      w = LA.mul (muStr ↥A O.toricRank m) u (LA.inv (muStr ↥A O.toricRank m) v) := ⟨_, rfl⟩
  have hw_pt : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of ↥A)} (x : SchemeHomOver s (muStr ↥A O.toricRank m)),
      NeronModelInfra.schemeHomOverComp x w =
        LA.mul s (NeronModelInfra.schemeHomOverComp x u) (LA.inv s (NeronModelInfra.schemeHomOverComp x v)) := by
    intro T s x
    rw [hcomp, hcomp, hcomp, hw, LA.mul_natural, inv_natural]
  have hw_mul : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) w =
        LA.mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) w)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) w) := by
    intro χ χ'
    letI : CommGroup (SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) :=
      { LA.pointGroup (barPt A) with mul_comm := hcommA (barPt A) }
    rw [hw_pt, hw_pt, hw_pt, hu, hv]
    set a := NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) u
    set b := NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) u
    set c := NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) v
    set d := NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) v
    show (a * b) * (c * d)⁻¹ = (a * c⁻¹) * (b * d⁻¹)
    rw [mul_inv, mul_mul_mul_comm]
  have hμκ : muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ muStr ↥A O.toricRank m =
      muStr (ResidueField ↥A) O.toricRank m ≫ resPt A := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x <;> simp
  have hw_special : muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ w.1 =
      muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ (LA.one (muStr ↥A O.toricRank m)).1 := by

    let sκ : SchemeHomOver (muStr (ResidueField ↥A) O.toricRank m ≫ resPt A) (muStr ↥A O.toricRank m) :=
      ⟨muBaseChange (IsLocalRing.residue ↥A) O.toricRank m, hμκ⟩
    have h1 : NeronModelInfra.schemeHomOverComp sκ u = NeronModelInfra.schemeHomOverComp sκ v := Subtype.ext huv
    have h2 := hw_pt sκ
    rw [h1] at h2
    letI := LA.pointGroup (muStr (ResidueField ↥A) O.toricRank m ≫ resPt A)
    have h3 : NeronModelInfra.schemeHomOverComp sκ w = LA.one _ := by rw [h2]; exact mul_inv_cancel _
    have h4 : NeronModelInfra.schemeHomOverComp sκ (LA.one (muStr ↥A O.toricRank m)) = LA.one _ := by
      rw [hcomp]; exact LA.one_natural _ _ _ _
    exact (congrArg Subtype.val h3).trans (congrArg Subtype.val h4).symm

  suffices hw1 : w = LA.one (muStr ↥A O.toricRank m) by
    letI := LA.pointGroup (muStr ↥A O.toricRank m)
    have : u * v⁻¹ = 1 := by
      show LA.mul _ u (LA.inv _ v) = LA.one _
      rw [← hw]; exact hw1
    exact mul_inv_eq_one.mp this

  haveI : IsReduced (AddMonoidAlgebra (AlgebraicClosure ℚ) (Fin O.toricRank → ZMod m)) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (AlgebraicClosure ℚ) _
  haveI : IsReduced (muCoord ↥A O.toricRank m) :=
    isReduced_of_injective (R := muCoord ↥A O.toricRank m)
      (S := AddMonoidAlgebra (AlgebraicClosure ℚ) (Fin O.toricRank → ZMod m))
      (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (algebraMap ↥A (AlgebraicClosure ℚ)))
      (AddMonoidAlgebra.map_injective (M := Fin O.toricRank → ZMod m)
        (algebraMap ↥A (AlgebraicClosure ℚ) : ↥A →+ AlgebraicClosure ℚ) Subtype.val_injective)
  haveI : IsReduced (Spec (CommRingCat.of (muCoord ↥A O.toricRank m))) := (affine_isReduced_iff _).mpr inferInstance
  haveI : Flat (muStr ↥A O.toricRank m) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap ↥A (muCoord ↥A O.toricRank m)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : LocallyOfFiniteType (muStr ↥A O.toricRank m) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    show (algebraMap ↥A (muCoord ↥A O.toricRank m)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance

  have hgl : ∀ (χ ψ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) (g : Fin O.toricRank → ZMod m),
      (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) = χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
    intro χ ψ g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have hone_gl : ∀ g : Fin O.toricRank → ZMod m,
      (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv (AddMonoidAlgebra.single g 1) = 1 := by
    intro g
    rw [AlgHom.convOne_def]
    simp [AddMonoidAlgebra.counit_single]
  have htors : ∀ χ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ), χ ^ m = 1 := by
    intro χ
    have hpow : ∀ (k : ℕ) (g : Fin O.toricRank → ZMod m),
        (χ ^ k).ofConv (AddMonoidAlgebra.single g 1) = (χ.ofConv (AddMonoidAlgebra.single g 1)) ^ k := by
      intro k g
      induction k with
      | zero => rw [pow_zero, pow_zero, hone_gl]
      | succ k ih => rw [pow_succ, hgl, ih, pow_succ]
    have hext : (χ ^ m).ofConv = (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv := by
      refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
      intro g
      rw [hpow, hone_gl, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
      have hmg : m • g = 0 := by
        funext j; simp
      rw [hmg]
      exact map_one χ.ofConv
    exact congrArg WithConv.toConv hext

  let pt : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))))
        (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
    fun χ => NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) w
  have hpt1 : ∀ χ, (pt χ).1 = Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ w.1 := fun χ => rfl
  have hpt_mul : ∀ χ χ', pt (χ * χ') = LA.mul _ (pt χ) (pt χ') := fun χ χ' => hw_mul χ χ'
  have hpt_one : pt 1 = LA.one _ := by
    apply eq_one_of_mul_self
    rw [← hpt_mul, mul_one]
  have hpt_eq : ∀ χ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      (⟨Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ w.1, by
          rw [Category.assoc, w.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2; exact χ.ofConv.comp_algebraMap⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))))
          (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) = pt χ := fun χ => Subtype.ext rfl
  have hwtors : LA.nsmul (muStr ↥A O.toricRank m) m w = LA.one _ := by
    refine GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_forall_withConv_point (AlgebraicClosure ℚ)
      (AlgebraicClosure ℚ) LA (muCoord ↥A O.toricRank m) w ?_ ?_ m htors
    · rw [hpt_eq]; exact hpt_one
    · intro χ χ'; rw [hpt_eq, hpt_eq, hpt_eq]; exact hpt_mul χ χ'
  have hwmem : w ∈ LA.torsionSubset (muStr ↥A O.toricRank m) m := (RelativeGroupLaw.mem_torsionSubset _ _ _ _).mpr hwtors

  obtain ⟨hLQF, hQC, hFlat⟩ :=
    ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange N₀ p hpN₀ A hA Λ hΛ O m hm
  haveI := hLQF; haveI := hQC; haveI := hFlat
  haveI : LocallyQuasiFinite (LA.schemeKerStr m) :=
    GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeKerStr_of_locallyQuasiFinite_schemeNsmul LA m
  haveI : QuasiCompact (LA.schemeKerStr m) :=
    GoodReductionJacobian.RelativeGroupLaw.quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul LA m
  haveI : Flat (LA.schemeKerStr m) := by
    show Flat (pullback.snd (LA.schemeNsmul m) _); infer_instance
  obtain ⟨H, _instCR, _instHopf, hHfin, hHflat, hHcocomm, jH, e, -, -, -, -, -, hinj, hsurj, he_mul, he_nat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing LA hcommA m
  haveI := hHfin; haveI := hHflat; haveI := hHcocomm
  haveI : Module.Free ↥A H := Module.free_of_flat_of_isLocalRing

  have he_one : ∀ (T : Type) [CommRing T] [Algebra ↥A T],
      ((e T 1).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) = LA.one _ := by
    intro T _ _
    apply eq_one_of_mul_self
    rw [← he_mul, mul_one]

  obtain ⟨φ₀c, hφ₀⟩ := hsurj (muCoord ↥A O.toricRank m) ⟨w, hwmem⟩
  set φ₀ : H →ₐ[↥A] muCoord ↥A O.toricRank m := φ₀c.ofConv with hφ₀def
  have hφ₀' : e (muCoord ↥A O.toricRank m) (WithConv.toConv φ₀) = ⟨w, hwmem⟩ := hφ₀
  have hθ : ∀ (T : Type) [CommRing T] [Algebra ↥A T] (θ : muCoord ↥A O.toricRank m →ₐ[↥A] T),
      ((e T (.toConv (θ.comp φ₀))).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA O.g)).1 =
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ w.1 := by
    intro T _ _ θ
    have h := he_nat (muCoord ↥A O.toricRank m) T θ (WithConv.toConv φ₀)
    rw [hφ₀'] at h
    exact h
  have hθ' : ∀ χ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      ((e _ (.toConv (χ.ofConv.comp φ₀))).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA O.g)) = pt χ :=
    fun χ => Subtype.ext ((hθ _ χ.ofConv).trans (hpt1 χ).symm)

  haveI : IsReduced ((AlgebraicClosure ℚ) ⊗[↥A] (muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m)) :=
    aux_isReduced_baseChange_tensor_addMonoidAlgebra (AlgebraicClosure ℚ) (Fin O.toricRank → ZMod m)
  haveI : NoZeroSMulDivisors ↥A (muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m) :=
    aux_noZeroSMulDivisors_of_free _
  have hsep : ∀ x : muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m,
      (∀ θ : muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, θ x = 0) → x = 0 :=
    fun x hx => Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct (AlgebraicClosure ℚ)
      (AlgebraicClosure ℚ) x hx
  have hinjA : Function.Injective (algebraMap ↥A (AlgebraicClosure ℚ)) := Subtype.val_injective
  have hone0 : (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv.comp φ₀ =
      (1 : WithConv (H →ₐ[↥A] AlgebraicClosure ℚ)).ofConv := by
    have h : e _ (.toConv ((1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv.comp φ₀)) = e _ 1 := by
      apply Subtype.ext
      rw [hθ' 1, hpt_one, he_one]
    exact congrArg WithConv.ofConv (hinj _ h)
  have hmul0 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      (χ * χ').ofConv.comp φ₀ =
        (WithConv.toConv (χ.ofConv.comp φ₀) * WithConv.toConv (χ'.ofConv.comp φ₀)).ofConv := by
    intro χ χ'
    have h : e _ (.toConv ((χ * χ').ofConv.comp φ₀)) =
        e _ (WithConv.toConv (χ.ofConv.comp φ₀) * WithConv.toConv (χ'.ofConv.comp φ₀)) := by
      apply Subtype.ext
      rw [hθ' (χ * χ'), he_mul, hθ' χ, hθ' χ', hpt_mul]
    exact congrArg WithConv.ofConv (hinj _ h)
  obtain ⟨φ, hφ⟩ := BialgHom.exists_coe_eq_of_forall_withConv_comp hinjA φ₀ hsep hone0 hmul0

  set κ := ResidueField ↥A with hκ
  set Tκ := muCoord κ O.toricRank m with hTκ
  let ψ₀ : muCoord ↥A O.toricRank m →ₐ[↥A] Tκ :=
    { AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (residue ↥A) with
      commutes' := fun r => by
        change AddMonoidAlgebra.mapRingHom _ (residue ↥A) (algebraMap ↥A (muCoord ↥A O.toricRank m) r) =
          algebraMap ↥A Tκ r
        rw [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
          Function.comp_apply, AddMonoidAlgebra.mapRingHom_single]
        rfl }
  have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀.toRingHom) = muBaseChange (residue ↥A) O.toricRank m := rfl
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap ↥A Tκ)) =
      muBaseChange (residue ↥A) O.toricRank m ≫ muStr ↥A O.toricRank m := by
    rw [IsScalarTower.algebraMap_eq ↥A κ Tκ, CommRingCat.ofHom_comp, Spec.map_comp]
    exact hμκ.symm
  have hone_cast : ∀ {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of ↥A)} (h : s = s'),
      (LA.one s).1 = (LA.one s').1 := by
    intro T s s' h; subst h; rfl
  have hcong : ∀ a : H, φ a - algebraMap ↥A _ (Coalgebra.counit a) ∈
      (IsLocalRing.maximalIdeal ↥A).map (algebraMap ↥A (muCoord ↥A O.toricRank m)) := by
    have h1 : ((e Tκ (.toConv (ψ₀.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m)))).val :
        SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA O.g)).1 =
          muBaseChange (residue ↥A) O.toricRank m ≫ (LA.one (muStr ↥A O.toricRank m)).1 := by
      rw [hφ, hθ Tκ ψ₀, hψ₀, hw_special]
    have h2 : ((e Tκ 1).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA O.g)).1 =
        muBaseChange (residue ↥A) O.toricRank m ≫ (LA.one (muStr ↥A O.toricRank m)).1 := by
      rw [he_one]
      first
        | exact (congrArg Subtype.val (LA.one_natural (muStr ↥A O.toricRank m) _
            (muBaseChange (residue ↥A) O.toricRank m) rfl)).symm
        | exact (hone_cast hbase).trans (congrArg Subtype.val (LA.one_natural (muStr ↥A O.toricRank m) _
            (muBaseChange (residue ↥A) O.toricRank m) rfl)).symm
    have h12 : e Tκ (.toConv (ψ₀.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m))) = e Tκ 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [h1, h2]
    have h3 : ψ₀.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m) =
        (Algebra.ofId ↥A Tκ).comp (Bialgebra.counitAlgHom ↥A H) := by
      have := hinj _ h12
      rw [AlgHom.convOne_def] at this
      exact WithConv.toConv_injective this
    intro a
    have hdiff : ψ₀ (φ a - algebraMap ↥A _ (Coalgebra.counit a)) = 0 := by
      have ha := congrArg (fun f : H →ₐ[↥A] Tκ => f a) h3
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply] at ha
      rw [map_sub, AlgHom.commutes, sub_eq_zero]
      exact ha
    apply mem_map_of_forall_apply_mem
    intro j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have hj := congrArg (fun y : Tκ => y.coeff j) hdiff
    change (AddMonoidAlgebra.mapRingHom _ (residue ↥A) _).coeff j = (0 : Tκ).coeff j at hj
    rwa [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero] at hj

  haveI : Algebra.Etale (↥A) (CartierDual (↥A) (muCoord ↥A O.toricRank m)) :=
    CartierDual.algebraEtale_addMonoidAlgebra (↥A) (Fin O.toricRank → ZMod m)
  have hrig := HopfAlgebra.bialgHom_apply_eq_algebraMap_counit_of_etale_cartierDual_of_sub_mem_map_maximalIdeal
    (muCoord ↥A O.toricRank m) H φ hcong
  have hφ1 : WithConv.toConv φ₀ = (1 : WithConv (H →ₐ[↥A] muCoord ↥A O.toricRank m)) := by
    rw [AlgHom.convOne_def]
    congr 1
    rw [← hφ]
    refine AlgHom.ext fun a => ?_
    rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
    exact hrig a
  have hfin : (⟨w, hwmem⟩ : LA.torsionSubset (muStr ↥A O.toricRank m) m) = e _ 1 := by
    rw [← hφ₀', hφ1]
  have := congrArg Subtype.val hfin
  rw [he_one] at this
  exact this

#print axioms solution

end S_ModularCurve_JZeroNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq (solution)
