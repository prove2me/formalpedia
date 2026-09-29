-- Prove2me | solution 1 for M4aHerbrand.infiniteIdele_tateCard_eq_localDegreeProd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9cbfc8a3-2713-594c-b841-6781e752eda7

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_InfiniteAdeleRing_BaseChangeData
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_infiniteIdele_tateCard_eq_localDegreeProd
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

noncomputable section

namespace M4aHerbrandArchnumSol

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge
open FLT.InfiniteAdeleBaseChange
open scoped TensorProduct

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

noncomputable def step1 :
    InfiniteAdeleRing L ≃+*
    ((p : (v : InfinitePlace K) ×
        {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
      p.2.1.Completion) :=
  (RingEquiv.piCongrLeft (fun w : InfinitePlace L => w.Completion)
    (Equiv.sigmaFiberEquiv
      (fun w : InfinitePlace L => InfinitePlace.comap w (algebraMap K L)))).symm

noncomputable def step2 :
    ((p : (v : InfinitePlace K) ×
        {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
      p.2.1.Completion) ≃+*
    ((v : InfinitePlace K) →
      (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion) where
  toFun x v w := x ⟨v, w⟩
  invFun y p := y p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

noncomputable def ringRegroup := (step1 K L).trans (step2 K L)

noncomputable def regroupUnits :
    (InfiniteAdeleRing L)ˣ ≃*
    (Π v : InfinitePlace K,
      (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ) :=
  (Units.mapEquiv (ringRegroup K L).toMulEquiv).trans MulEquiv.piUnits

abbrev teInf : ((InfiniteAdeleRing K) ⊗[K] L) ≃+* InfiniteAdeleRing L :=
  (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv

abbrev teF : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] L) ≃+* FiniteAdeleRing (𝓞 L) L :=
  finiteBaseChangeRingEquiv (𝓞 K) K L (𝓞 L)

abbrev oneTensorInf (τ : L ≃ₐ[K] L) :
    ((InfiniteAdeleRing K) ⊗[K] L) ≃+* ((InfiniteAdeleRing K) ⊗[K] L) :=
  (Algebra.TensorProduct.congr
    (AlgEquiv.refl : InfiniteAdeleRing K ≃ₐ[K] InfiniteAdeleRing K) τ).toRingEquiv

omit [NumberField K] [NumberField L] in
theorem oneTensorInf_tmul (τ : L ≃ₐ[K] L) (x : InfiniteAdeleRing K) (l : L) :
    oneTensorInf K L τ (x ⊗ₜ l) = x ⊗ₜ τ l := rfl

def actInf (τ : L ≃ₐ[K] L) : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L :=
  (teInf K L).symm.trans ((oneTensorInf K L τ).trans (teInf K L))

theorem actInf_teInf (τ : L ≃ₐ[K] L) (t : (InfiniteAdeleRing K) ⊗[K] L) :
    actInf K L τ (teInf K L t) = teInf K L (oneTensorInf K L τ t) := by
  show teInf K L (oneTensorInf K L τ ((teInf K L).symm (teInf K L t))) = _
  rw [RingEquiv.symm_apply_apply]

theorem genuineTensorEquiv_fst (z : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    (letI := (genuineβ K L).toAlgebra; (genuineTensorEquiv K L z).1) =
      teInf K L ((prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L z).1) := rfl

omit [NumberField L] in
theorem prodTensorAlgEquiv_fst_oneTensor (τ : L ≃ₐ[K] L) (y : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L
        ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : AdeleRing (𝓞 K) K ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 K) K) τ) y)).1 =
      oneTensorInf K L τ (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L y).1 := by
  have h0 : (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L)
      (0 : (AdeleRing (𝓞 K) K) ⊗[K] L) = 0 := map_zero _
  have hadd' : ∀ c d : (AdeleRing (𝓞 K) K) ⊗[K] L,
      (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L) (c + d) =
        (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L) c +
          (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L) d :=
    fun c d => map_add _ c d
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, h0, Prod.fst_zero, map_zero]
  | tmul p l =>
    have hc : (Algebra.TensorProduct.congr
        (AlgEquiv.refl : AdeleRing (𝓞 K) K ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 K) K) τ) (p ⊗ₜ l) = p ⊗ₜ τ l := rfl
    rw [hc]
    exact (congrArg Prod.fst (prodTensorAlgEquiv_tmul K (InfiniteAdeleRing K)
        (FiniteAdeleRing (𝓞 K) K) L p (τ l))).trans
      (congrArg (fun q : ((InfiniteAdeleRing K) ⊗[K] L) × ((FiniteAdeleRing (𝓞 K) K) ⊗[K] L) =>
          oneTensorInf K L τ q.1)
        (prodTensorAlgEquiv_tmul K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L p l)).symm
  | add a b ha hb => rw [map_add, hadd', hadd', Prod.fst_add, Prod.fst_add, ha, hb, map_add]

theorem fst_genuineAct (τ : L ≃ₐ[K] L) (z : AdeleRing (𝓞 L) L) :
    (letI := (genuineβ K L).toAlgebra;
      ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act τ z).1) = actInf K L τ z.1 := by
  letI := (genuineβ K L).toAlgebra
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act]
  have hS : (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L
      ((genuineTensorEquiv K L).symm z)).1 = (teInf K L).symm z.1 := by
    have h := (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L).toRingEquiv.apply_symm_apply
      ((RingEquiv.prodCongr (teInf K L) (teF K L)).symm z)
    exact congrArg Prod.fst h
  show (genuineTensorEquiv K L ((Algebra.TensorProduct.congr AlgEquiv.refl τ)
      ((genuineTensorEquiv K L).symm z))).1 = actInf K L τ z.1
  rw [genuineTensorEquiv_fst, prodTensorAlgEquiv_fst_oneTensor, hS]
  rfl

def piVInf (v : InfinitePlace K) :
    InfiniteAdeleRing L →+*
    ((w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) → w.1.Completion) :=
  RingHom.pi fun w => Pi.evalRingHom (fun w' : InfinitePlace L => w'.Completion) w.1

omit [NumberField K] [NumberField L] in
theorem piVInf_apply (v : InfinitePlace K) (y : InfiniteAdeleRing L)
    (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    piVInf K L v y w = y w.1 := rfl

abbrev placeEq (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) ≃+*
    ((w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) → w.1.Completion) :=
  (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).placeEquiv v

theorem piVInf_teInf (v : InfinitePlace K) (z : (InfiniteAdeleRing K) ⊗[K] L) :
    piVInf K L v (teInf K L z) = placeEq K L v (tensorPiAlgHom K L z v) := by
  funext w
  obtain ⟨w1, hw⟩ := w
  subst hw
  rfl

abbrev oneTensorV (v : InfinitePlace K) (τ : L ≃ₐ[K] L) :
    (v.Completion ⊗[K] L) ≃+* (v.Completion ⊗[K] L) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[K] v.Completion) τ).toRingEquiv

omit [NumberField K] [NumberField L] in
theorem oneTensorV_tmul (v : InfinitePlace K) (τ : L ≃ₐ[K] L) (a : v.Completion) (l : L) :
    oneTensorV K L v τ (a ⊗ₜ l) = a ⊗ₜ τ l := rfl

def rhoVInf (v : InfinitePlace K) (τ : L ≃ₐ[K] L) :
    ((w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) → w.1.Completion) ≃+*
    ((w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) → w.1.Completion) :=
  (placeEq K L v).symm.trans ((oneTensorV K L v τ).trans (placeEq K L v))

theorem rhoVInf_placeEq (v : InfinitePlace K) (τ : L ≃ₐ[K] L) (t : v.Completion ⊗[K] L) :
    rhoVInf K L v τ (placeEq K L v t) = placeEq K L v (oneTensorV K L v τ t) := by
  show placeEq K L v (oneTensorV K L v τ ((placeEq K L v).symm (placeEq K L v t))) = _
  rw [RingEquiv.symm_apply_apply]

omit [NumberField K] [NumberField L] in

theorem tensorPi_oneTensorInf (τ : L ≃ₐ[K] L) (z : (InfiniteAdeleRing K) ⊗[K] L)
    (v : InfinitePlace K) :
    tensorPiAlgHom K L (oneTensorInf K L τ z) v = oneTensorV K L v τ (tensorPiAlgHom K L z v) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul x l => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem piVInf_actInf (v : InfinitePlace K) (τ : L ≃ₐ[K] L) (y : InfiniteAdeleRing L) :
    piVInf K L v (actInf K L τ y) = rhoVInf K L v τ (piVInf K L v y) := by
  obtain ⟨z, rfl⟩ := (teInf K L).surjective y
  rw [actInf_teInf, piVInf_teInf, piVInf_teInf, tensorPi_oneTensorInf, rhoVInf_placeEq]

section Transport

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerCongr (e : A ≃+ B) (f : A →+ A) (f' : B →+ B) (hf : ∀ a, f' (e a) = e (f a)) :
    f.ker ≃+ f'.ker where
  toFun x := ⟨e x, by
    rw [AddMonoidHom.mem_ker, hf, (AddMonoidHom.mem_ker).mp x.2, map_zero]⟩
  invFun y := ⟨e.symm y, by
    rw [AddMonoidHom.mem_ker]
    apply e.injective
    rw [← hf, e.apply_symm_apply, (AddMonoidHom.mem_ker).mp y.2, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : A))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : B))
  map_add' x y := Subtype.ext (map_add e (x : A) (y : A))

theorem coe_kerCongr (e : A ≃+ B) (f : A →+ A) (f' : B →+ B) (hf : ∀ a, f' (e a) = e (f a))
    (x : f.ker) : ((kerCongr e f f' hf x : f'.ker) : B) = e x := rfl

theorem coe_kerCongr_symm (e : A ≃+ B) (f : A →+ A) (f' : B →+ B) (hf : ∀ a, f' (e a) = e (f a))
    (y : f'.ker) : (((kerCongr e f f' hf).symm y : f.ker) : A) = e.symm y := rfl

theorem card_quot_conj (e : A ≃+ B) (f g : A →+ A) (f' g' : B →+ B)
    (hf : ∀ a, f' (e a) = e (f a)) (hg : ∀ a, g' (e a) = e (g a)) :
    Nat.card (↥f.ker ⧸ g.range.addSubgroupOf f.ker) =
      Nat.card (↥f'.ker ⧸ g'.range.addSubgroupOf f'.ker) := by
  change (g.range.addSubgroupOf f.ker).index = (g'.range.addSubgroupOf f'.ker).index
  have hmap : (g.range.addSubgroupOf f.ker).map
      ((kerCongr e f f' hf : f.ker ≃+ f'.ker) : f.ker →+ f'.ker) = g'.range.addSubgroupOf f'.ker := by
    ext y
    rw [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hx
      obtain ⟨a, ha⟩ := hx
      refine ⟨e a, ?_⟩
      rw [hg, ha]
      rfl
    · rintro ⟨b, hb⟩
      refine ⟨(kerCongr e f f' hf).symm y, ?_, AddEquiv.apply_symm_apply _ _⟩
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
      refine ⟨e.symm b, e.injective ?_⟩
      rw [← hg, e.apply_symm_apply, hb, coe_kerCongr_symm, e.apply_symm_apply]
  rw [← hmap, AddSubgroup.index_map_equiv]

theorem tate_card_conj (e : A ≃+ B) (d N : A →+ A) (d' N' : B →+ B)
    (hd' : ∀ a, d' (e a) = e (d a)) (hN' : ∀ a, N' (e a) = e (N a)) :
    (Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
      = Nat.card (↥d'.ker ⧸ N'.range.addSubgroupOf d'.ker))
    ∧ (Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker)
      = Nat.card (↥N'.ker ⧸ d'.range.addSubgroupOf N'.ker)) :=
  ⟨card_quot_conj e d N d' N' hd' hN', card_quot_conj e N d N' d' hN' hd'⟩

end Transport

section Dock

variable (σ : L ≃ₐ[K] L)
variable (Φ : (InfiniteAdeleRing L)ˣ ≃* (InfiniteAdeleRing L)ˣ)

omit [NumberField K] [NumberField L] in

theorem regroupUnits_coe (u : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K)
    (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    ((regroupUnits K L u v :
      ((w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion)ˣ) :
      (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion) w = (u : InfiniteAdeleRing L) w.1 := rfl

omit [NumberField K] [NumberField L] in

theorem regroupUnits_coe_piVInf (u : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K) :
    ((regroupUnits K L u v :
      ((w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion)ˣ) :
      (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion) = piVInf K L v (u : InfiniteAdeleRing L) := rfl

theorem Phi_eq_actInf
    (hΦ : ∀ x : (InfiniteAdeleRing L)ˣ,
      ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
        (((x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L),
          (1 : FiniteAdeleRing (𝓞 L) L))).1
        = ((Φ x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L))
    (x : (InfiniteAdeleRing L)ˣ) :
    ((Φ x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) =
      actInf K L σ ((x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) := by
  rw [← hΦ x]
  exact fst_genuineAct K L σ (((x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L),
    (1 : FiniteAdeleRing (𝓞 L) L))

theorem regroup_Phi
    (hΦ : ∀ x : (InfiniteAdeleRing L)ˣ,
      ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
        (((x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L),
          (1 : FiniteAdeleRing (𝓞 L) L))).1
        = ((Φ x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L))
    (x : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K) :
    regroupUnits K L (Φ x) v =
      Units.mapEquiv (rhoVInf K L v σ).toMulEquiv (regroupUnits K L x v) := by
  apply Units.ext
  have h1 : ((regroupUnits K L (Φ x) v : _ˣ) :
      (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion) = piVInf K L v ((Φ x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) :=
    regroupUnits_coe_piVInf K L (Φ x) v
  have h2 : ((Units.mapEquiv (rhoVInf K L v σ).toMulEquiv (regroupUnits K L x v) : _ˣ) :
      (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion) = rhoVInf K L v σ (piVInf K L v ((x : (InfiniteAdeleRing L)ˣ) :
        InfiniteAdeleRing L)) := by
    rw [← regroupUnits_coe_piVInf]
    rfl
  rw [h1, h2, Phi_eq_actInf K L σ Φ hΦ x, piVInf_actInf]

theorem regroup_Phi_pow
    (hΦ : ∀ x : (InfiniteAdeleRing L)ˣ,
      ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
        (((x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L),
          (1 : FiniteAdeleRing (𝓞 L) L))).1
        = ((Φ x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L))
    (i : ℕ) (x : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K) :
    regroupUnits K L ((Φ ^ i) x) v =
      ((Units.mapEquiv (rhoVInf K L v σ).toMulEquiv) ^ i) (regroupUnits K L x v) := by
  induction i generalizing x with
  | zero => rfl
  | succ n ih =>
    have hl : (Φ ^ (n + 1)) x = (Φ ^ n) (Φ x) := by
      rw [pow_succ]; rfl
    have hr : ((Units.mapEquiv (rhoVInf K L v σ).toMulEquiv) ^ (n + 1))
        (regroupUnits K L x v) =
        ((Units.mapEquiv (rhoVInf K L v σ).toMulEquiv) ^ n)
          (Units.mapEquiv (rhoVInf K L v σ).toMulEquiv (regroupUnits K L x v)) := by
      rw [pow_succ]; rfl
    rw [hl, hr, ih (Φ x), regroup_Phi K L σ Φ hΦ x v]

end Dock

end M4aHerbrandArchnumSol

end

open NumberField IsDedekindDomain M4aHerbrandArchnumSol in
theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (Φ : (InfiniteAdeleRing L)ˣ ≃* (InfiniteAdeleRing L)ˣ)
    (hΦ : ∀ x : (InfiniteAdeleRing L)ˣ,
      (D.act σ (((x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L),
        (1 : FiniteAdeleRing (𝓞 L) L))).1
        = ((Φ x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L))

    (d : Additive (InfiniteAdeleRing L)ˣ →+ Additive (InfiniteAdeleRing L)ˣ)
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul (Φ u) - Additive.ofMul u)
    (N : Additive (InfiniteAdeleRing L)ˣ →+ Additive (InfiniteAdeleRing L)ˣ)
    (hN : ∀ u, N (Additive.ofMul u)
      = ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), Additive.ofMul ((Φ ^ i) u))

    (si : InfinitePlace K → ℕ)
    (hsi : ∀ v, si v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / si v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  classical
  haveI : Subsingleton (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L :=
    Subsingleton.elim _ _

  set e := MulEquiv.toAdditive (regroupUnits K L) with he

  set d' := (e.toAddMonoidHom.comp d).comp e.symm.toAddMonoidHom with hd'def
  set N' := (e.toAddMonoidHom.comp N).comp e.symm.toAddMonoidHom with hN'def

  have hPhiA : ∀ (v : InfinitePlace K)
      (u : ((w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
        w.1.Completion)ˣ)
      (x : InfiniteAdeleRing L),
      (∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        x w.1 = (u : (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
          w.1.Completion) w) →
      ∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
          (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 w.1 =
          (Units.mapEquiv (rhoVInf K L v σ).toMulEquiv u :
            (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
              w.1.Completion) w := by
    intro v u x hx w
    have h1 : ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
        (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 = actInf K L σ x :=
      fst_genuineAct K L σ (x, (1 : FiniteAdeleRing (𝓞 L) L))
    have h2 : actInf K L σ x w.1 = piVInf K L v (actInf K L σ x) w := rfl
    have h3 : piVInf K L v x =
        (u : (w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) →
          w.1.Completion) := by
      funext w'
      exact hx w'
    rw [h1, h2, piVInf_actInf, h3]
    rfl

  have hd'' : ∀ u, d' (Additive.ofMul u) =
      Additive.ofMul ((fun v => Units.mapEquiv (rhoVInf K L v σ).toMulEquiv (u v))) -
        Additive.ofMul u := by
    intro u
    show e (d (e.symm (Additive.ofMul u))) = _
    have h1 : e.symm (Additive.ofMul u) =
        Additive.ofMul ((regroupUnits K L).symm u) := rfl
    rw [h1, hd ((regroupUnits K L).symm u)]
    have h2 : e (Additive.ofMul (Φ ((regroupUnits K L).symm u)) -
        Additive.ofMul ((regroupUnits K L).symm u)) =
        Additive.ofMul (regroupUnits K L (Φ ((regroupUnits K L).symm u))) -
          Additive.ofMul (regroupUnits K L ((regroupUnits K L).symm u)) := map_sub e _ _
    rw [h2, (regroupUnits K L).apply_symm_apply]
    congr 2
    funext v
    rw [regroup_Phi K L σ Φ hΦ ((regroupUnits K L).symm u) v,
      (regroupUnits K L).apply_symm_apply]
  have hN'' : ∀ u, N' (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v =>
          ((Units.mapEquiv (rhoVInf K L v σ).toMulEquiv) ^ i) (u v))) := by
    intro u
    show e (N (e.symm (Additive.ofMul u))) = _
    have h1 : e.symm (Additive.ofMul u) =
        Additive.ofMul ((regroupUnits K L).symm u) := rfl
    rw [h1, hN ((regroupUnits K L).symm u), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show Additive.ofMul (regroupUnits K L ((Φ ^ i) ((regroupUnits K L).symm u))) = _
    congr 1
    funext v
    rw [regroup_Phi_pow K L σ Φ hΦ i ((regroupUnits K L).symm u) v,
      (regroupUnits K L).apply_symm_apply]

  have hconj_d : ∀ a, d' (e a) = e (d a) := by
    intro a
    show e (d (e.symm (e a))) = e (d a)
    rw [e.symm_apply_apply]
  have hconj_N : ∀ a, N' (e a) = e (N a) := by
    intro a
    show e (N (e.symm (e a))) = e (N a)
    rw [e.symm_apply_apply]
  obtain ⟨hc0, hc1⟩ := tate_card_conj e d N d' N' hconj_d hconj_N
  obtain ⟨h0', h1'⟩ := M4aHerbrand.infiniteIdeleFibre_tateCard_eq_localDegreeProd K L σ hσ
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)
    (fun v => Units.mapEquiv (rhoVInf K L v σ).toMulEquiv) hPhiA d' hd'' N' hN'' si hsi
  exact ⟨hc0.trans h0', hc1.trans h1'⟩

section Battery
#print axioms solution
#print axioms M4aHerbrandArchnumSol.regroupUnits
#print axioms M4aHerbrandArchnumSol.fst_genuineAct
#print axioms M4aHerbrandArchnumSol.piVInf_actInf
#print axioms M4aHerbrandArchnumSol.regroup_Phi
#print axioms M4aHerbrandArchnumSol.tate_card_conj
end Battery

end S_M4aHerbrand_infiniteIdele_tateCard_eq_localDegreeProd
end P2MW
export P2MW.S_M4aHerbrand_infiniteIdele_tateCard_eq_localDegreeProd (solution)
