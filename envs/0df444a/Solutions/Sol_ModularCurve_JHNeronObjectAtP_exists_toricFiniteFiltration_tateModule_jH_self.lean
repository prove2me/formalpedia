-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_toricFiniteFiltration_tateModule_jH_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5a241082-5652-5b2e-a606-3a4d231c7cd9

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPts_le_torsion
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_genOpH_mem_toricPts
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts
import Theorems.Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_toricFiniteFiltration_tateModule_jH_self
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

noncomputable section

namespace QPARN

open ModularCurve.JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

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
  · unfold JHNeronObjectAtP.toricPoint
    rw [Equiv.apply_symm_apply]
    change (RelativeGroupLaw.baseChangePointToBase Λ.σA _).1 = _
    rw [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe]
    change (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ ι.1) ≫ _ = _
    rw [hfac, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc]

theorem toricPts_le_finPts (m : ℕ) : O.toricPts m ≤ O.finPts m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [JHNeronObjectAtP.toricPts, dif_neg (lt_irrefl 0)]
    exact bot_le
  have hmem := (ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
    p M H hpM A hA Λ O m).1
  have htors := ModularCurve.JHNeronObjectAtP.toricPts_le_torsion p M H hpM A hA Λ O m
  intro x hx
  have hx' := hx
  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx'
  refine AddSubgroup.closure_le (K := O.finPts m) |>.2 ?_ hx'
  rintro _ ⟨χ, rfl⟩
  refine (hmem _).2 ⟨htors ?_, extendsToPlace_toricPoint O hm χ⟩
  rw [JHNeronObjectAtP.toricPts, dif_pos hm]
  exact AddSubgroup.subset_closure ⟨χ, rfl⟩

theorem genOpH_mem_finPts (S : Set ℕ) (g : CohCarrier.Gen M S) (m : ℕ) (x : JH M H)
    (hx : x ∈ O.finPts m) : genOpH M H S g x ∈ O.finPts m := by
  let φ : SchemeHomOver O.g O.g := O.hecke S g
  let W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
    NeronSpecialFibreInfra.fibreRestrictAlong Λ.σA O.g O.g φ
  have hcomp : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of ↥A)}
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      RelativeGroupLaw.baseChangePointToBase Λ.σA (NeronModelInfra.schemeHomOverComp x W) =
        NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase Λ.σA x) φ :=
    fun x => RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong Λ.σA φ x
  have hinj : ∀ {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of ↥A)},
      Function.Injective (RelativeGroupLaw.baseChangePointToBase Λ.σA (f := O.g) (t' := s)) :=
    fun {T} {s} a b h => by
      have h' := congrArg (RelativeGroupLaw.baseChangePointOfBase Λ.σA) h
      rwa [RelativeGroupLaw.baseChangePointOfBase_toBase, RelativeGroupLaw.baseChangePointOfBase_toBase] at h'
  have hWmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W)
          (NeronModelInfra.schemeHomOverComp y W) := by
    intro T s x y
    apply hinj
    rw [hcomp, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase,
      O.hecke_mul, hcomp, hcomp]
  have hWpts : ∀ x : JH M H, O.pts (genOpH M H S g x) =
      genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W) := by
    intro x
    apply Subtype.ext
    rw [O.hecke_pts]
    unfold genOfBaseChangePt
    rw [hcomp, RelativeGroupLaw.baseChangePointToBase_ofBase]
    rfl
  exact (ModularCurve.JHNeronObjectAtP.mem_finPts_and_mem_toricPts_of_schemeHomOver_baseChange_pts
    p M H hpM A hA Λ O W hWmul (genOpH M H S g) hWpts).1 m x hx

theorem smul_mem_toricPts_of_mem_decompositionSubgroup {m : ℕ}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (x : JH M H) (hx : x ∈ O.toricPts m) : σ • x ∈ O.toricPts m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [JHNeronObjectAtP.toricPts, dif_neg (lt_irrefl 0)] at hx ⊢
    rw [(AddSubgroup.mem_bot).1 hx,
      show σ • (0 : JH M H) = 0 from map_zero (DistribSMul.toAddMonoidHom (JH M H) σ)]
    exact zero_mem _
  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx ⊢
  have hle : AddSubgroup.closure (Set.range (O.toricPoint m hm)) ≤
      (AddSubgroup.closure (Set.range (O.toricPoint m hm))).comap
        (DistribSMul.toAddMonoidHom (JH M H) σ) := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨χ, rfl⟩
    obtain ⟨χ', hχ'⟩ := O.toricLift_dec m hm σ hσ χ
    rw [AddSubgroup.coe_comap, Set.mem_preimage, DistribSMul.toAddMonoidHom_apply]
    change σ • O.toricPoint m hm χ ∈ _
    unfold JHNeronObjectAtP.toricPoint
    rw [hχ']
    exact AddSubgroup.subset_closure ⟨χ', rfl⟩
  exact hle hx

theorem smul_mem_finPts_of_mem_decompositionSubgroup
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ)) {m : ℕ}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (x : JH M H) (hx : x ∈ O.finPts m) : σ • x ∈ O.finPts m := by
  have hmem := (ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
    p M H hpM A hA Λ O m).1
  obtain ⟨htor, s, hs⟩ := (hmem x).1 hx
  refine (hmem _).2 ⟨?_, ?_⟩
  · rw [Pic0.mem_torsion] at htor ⊢
    change (m : ℤ) • DistribSMul.toAddMonoidHom (JH M H) σ x = 0
    rw [← map_zsmul, htor, map_zero]
  · let τ : ↥A →+* ↥A :=
      MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) ↥A ⟨σ, hσ⟩
    have hτ : ∀ a : ↥A, ((τ a : ↥A) : AlgebraicClosure ℚ) = σ a := fun _ => rfl
    have hτρ : τ.comp ρ = ρ := by
      refine RingHom.ext fun r => Subtype.ext ?_
      rw [RingHom.comp_apply, hτ]
      have h1 : ((ρ r : ↥A) : AlgebraicClosure ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) r := by
        rw [← hρ]; rfl
      rw [h1, IsScalarTower.algebraMap_apply (R p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]
    have hsub : (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype = A.subtype.comp τ :=
      RingHom.ext fun a => (hτ a).symm
    refine ⟨⟨Spec.map (CommRingCat.ofHom τ) ≫ s.1, ?_⟩, ?_⟩
    · rw [Category.assoc, s.2, hσA, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hτρ]
    · rw [O.pts_galois, hs, ← Category.assoc, ← Category.assoc]
      congr 1
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hsub]

theorem inertia_smul_eq_of_mem_toricPts {m : ℕ} (hm : 0 < m)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (c : ℕ)
    (hc : ∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c)
    (x : JH M H) (hx : x ∈ O.toricPts m) : σ • x = c • x := by
  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx
  let f : JH M H →+ JH M H := DistribSMul.toAddMonoidHom (JH M H) σ
  let g : JH M H →+ JH M H := DistribSMul.toAddMonoidHom (JH M H) c
  have hle : AddSubgroup.closure (Set.range (O.toricPoint m hm)) ≤ f.eqLocus g := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨χ, rfl⟩
    change f (O.toricPoint m hm χ) = g (O.toricPoint m hm χ)
    exact O.toricLift_inertia m hm σ hσ c hc χ
  exact hle hx

def levelwise (P : ℕ → AddSubgroup (JH M H)) : Submodule ℤ_[p] (TateModule p (JH M H)) where
  carrier := {x | ∀ n, (x : ℕ → JH M H) n ∈ P (p ^ n)}
  add_mem' := fun {x y} hx hy n => by
    rw [AddSubgroup.coe_add, Pi.add_apply]
    exact add_mem (hx n) (hy n)
  zero_mem' := fun n => by
    rw [AddSubgroup.coe_zero, Pi.zero_apply]
    exact zero_mem _
  smul_mem' := fun a x hx n => by
    change ((a • x : TateModule p (JH M H)) : ℕ → JH M H) n ∈ P (p ^ n)
    rw [TateModule.smul_apply]
    exact zsmul_mem (hx n) _

theorem mem_levelwise (P : ℕ → AddSubgroup (JH M H)) (x : TateModule p (JH M H)) :
    x ∈ levelwise (p := p) (M := M) (H := H) P ↔ ∀ n, (x : ℕ → JH M H) n ∈ P (p ^ n) := Iff.rfl

end QPARN

end

theorem QPARN.val_toZModPow_eq_appr {p : ℕ} [Fact p.Prime] (n : ℕ) (a : ℤ_[p]) :
    (PadicInt.toZModPow n a).val = a.appr n := by
  change ((a.appr n : ℕ) : ZMod (p ^ n)).val = a.appr n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt a n)]

open QPARN in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (S : Set ℕ)

    (hinertF : ∀ (m : ℕ), 0 < m → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      ∀ x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m, σ • x - x ∈ O.finPts m) :
    ∃ (Tt Tf : Submodule ℤ_[p] (TateModule p (JH M H))),
      (∀ x : TateModule p (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.toricPts (p ^ n)) ∧
      (∀ x : TateModule p (JH M H), x ∈ Tf ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.finPts (p ^ n)) ∧
      Tt ≤ Tf ∧
      (∀ (g : CohCarrier.Gen M S) (x : TateModule p (JH M H)),
        (x ∈ Tt → tateGenOpH M H S p g x ∈ Tt) ∧ (x ∈ Tf → tateGenOpH M H S p g x ∈ Tf)) ∧

      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x : TateModule p (JH M H),
        (x ∈ Tt → JH.tateGaloisRep M H p σ x ∈ Tt) ∧ (x ∈ Tf → JH.tateGaloisRep M H p σ x ∈ Tf)) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : TateModule p (JH M H), JH.tateGaloisRep M H p σ x - x ∈ Tf) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ Tt, JH.tateGaloisRep M H p σ x =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨levelwise O.toricPts, levelwise O.finPts, fun x => Iff.rfl, fun x => Iff.rfl, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx n
    exact toricPts_le_finPts O (p ^ n) (hx n)
  ·
    intro g x
    refine ⟨fun hx n => ?_, fun hx n => ?_⟩
    · rw [tateGenOpH_apply_coe]
      exact ModularCurve.JHNeronObjectAtP.genOpH_mem_toricPts p M H hpM A hA Λ hΛ O S (p ^ n) (pow_pos hp.pos n)
        g _ (hx n)
    · rw [tateGenOpH_apply_coe]
      exact genOpH_mem_finPts O S g (p ^ n) _ (hx n)
  ·
    intro σ hσD x
    refine ⟨fun hx n => ?_, fun hx n => ?_⟩
    · rw [JH.tateGaloisRep_apply_coe]
      exact smul_mem_toricPts_of_mem_decompositionSubgroup O σ hσD _ (hx n)
    · rw [JH.tateGaloisRep_apply_coe]
      exact smul_mem_finPts_of_mem_decompositionSubgroup O ρ hρ hσ σ hσD _ (hx n)
  ·
    intro σ hσI x n
    rw [AddSubgroup.coe_sub, Pi.sub_apply, JH.tateGaloisRep_apply_coe]
    refine hinertF (p ^ n) (pow_pos hp.pos n) σ hσI _ ?_
    rw [Pic0.mem_torsion]
    exact TateModule.torsion x n
  ·
    intro σ hσI x hx
    refine Subtype.ext (funext fun n => ?_)
    rw [JH.tateGaloisRep_apply_coe, TateModule.smul_apply]
    have hc : ∀ ζ : AlgebraicClosure ℚ, ζ ^ (p ^ n) = 1 → σ ζ =
        ζ ^ ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n := by
      intro ζ hζ
      have h := cyclotomicCharacter.spec p (n := n) σ.toRingEquiv ζ hζ
      rw [val_toZModPow_eq_appr] at h
      exact h
    rw [inertia_smul_eq_of_mem_toricPts O (pow_pos hp.pos n) σ hσI _ hc _ (hx n), natCast_zsmul]

end S_ModularCurve_JHNeronObjectAtP_exists_toricFiniteFiltration_tateModule_jH_self
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_toricFiniteFiltration_tateModule_jH_self (solution)
