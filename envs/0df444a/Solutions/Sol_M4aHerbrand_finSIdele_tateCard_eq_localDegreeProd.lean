-- Prove2me | solution 1 for M4aHerbrand.finSIdele_tateCard_eq_localDegreeProd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0e2b6481-9a72-5680-bdaa-0d10eae3e8dc

import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_finSIdele_tateCard_eq_localDegreeProd
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

open NumberField IsDedekindDomain

set_option maxHeartbeats 6400000 in

private theorem M4aHerbrandFinnumSol.supplier_finFibreBox
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = (u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          w.1.adicCompletion L) w) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          (Φf v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            w.1.adicCompletion L) w)

    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = ((u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          ((Φb v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))

    (d : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))) - Additive.ofMul u)
    (N : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))))

    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  exact M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd K L σ hσ S hSram D Φf hΦf Φb hΦb d hd N hN sf hsf

noncomputable section

namespace M4aHerbrandFinnumSol

open IsDedekindDomain.HeightOneSpectrum M4aHerbrand.Bridge M4aHerbrand.GenuineDescent
open scoped TensorProduct

section Transport

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

private def kerCongr (e : A ≃+ B) (f : A →+ A) (f' : B →+ B) (hf : ∀ a, f' (e a) = e (f a)) :
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

private theorem coe_kerCongr (e : A ≃+ B) (f : A →+ A) (f' : B →+ B) (hf : ∀ a, f' (e a) = e (f a))
    (x : f.ker) : ((kerCongr e f f' hf x : f'.ker) : B) = e x := rfl

private theorem coe_kerCongr_symm (e : A ≃+ B) (f : A →+ A) (f' : B →+ B) (hf : ∀ a, f' (e a) = e (f a))
    (y : f'.ker) : (((kerCongr e f f' hf).symm y : f.ker) : A) = e.symm y := rfl

private theorem card_quot_conj (e : A ≃+ B) (f g : A →+ A) (f' g' : B →+ B)
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

private theorem tate_card_conj (e : A ≃+ B) (d N : A →+ A) (d' N' : B →+ B)
    (hd' : ∀ a, d' (e a) = e (d a)) (hN' : ∀ a, N' (e a) = e (N a)) :
    (Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
      = Nat.card (↥d'.ker ⧸ N'.range.addSubgroupOf d'.ker))
    ∧ (Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker)
      = Nat.card (↥N'.ker ⧸ d'.range.addSubgroupOf N'.ker)) :=
  ⟨card_quot_conj e d N d' N' hd' hN', card_quot_conj e N d N' d' hN' hd'⟩

end Transport

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] moduleFinite_ringOfIntegers

section ActFin

private abbrev teF : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] L) ≃+* FiniteAdeleRing (𝓞 L) L :=
  finiteBaseChangeRingEquiv (𝓞 K) K L (𝓞 L)

private abbrev oneTensor (τ : L ≃ₐ[K] L) :
    ((FiniteAdeleRing (𝓞 K) K) ⊗[K] L) ≃+* ((FiniteAdeleRing (𝓞 K) K) ⊗[K] L) :=
  (Algebra.TensorProduct.congr
    (AlgEquiv.refl : FiniteAdeleRing (𝓞 K) K ≃ₐ[K] FiniteAdeleRing (𝓞 K) K) τ).toRingEquiv

omit [NumberField L] in
private theorem oneTensor_tmul (τ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 K) K) (l : L) :
    oneTensor K L τ (x ⊗ₜ l) = x ⊗ₜ τ l := rfl

private def actFin (τ : L ≃ₐ[K] L) : FiniteAdeleRing (𝓞 L) L ≃+* FiniteAdeleRing (𝓞 L) L :=
  (teF K L).symm.trans ((oneTensor K L τ).trans (teF K L))

private theorem actFin_teF (τ : L ≃ₐ[K] L) (t : (FiniteAdeleRing (𝓞 K) K) ⊗[K] L) :
    actFin K L τ (teF K L t) = teF K L (oneTensor K L τ t) := by
  show teF K L (oneTensor K L τ ((teF K L).symm (teF K L t))) = _
  rw [RingEquiv.symm_apply_apply]

private theorem teF_tmul (x : FiniteAdeleRing (𝓞 K) K) (l : L) :
    teF K L (x ⊗ₜ l) = finiteConorm (𝓞 K) K L (𝓞 L) x * algebraMap L (FiniteAdeleRing (𝓞 L) L) l := by
  have h : x ⊗ₜ[K] l = (x ⊗ₜ[K] (1 : L)) * ((1 : FiniteAdeleRing (𝓞 K) K) ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, finiteBaseChangeRingEquiv_tmul_one, finiteBaseChangeRingEquiv_one_tmul]

private theorem actFin_conorm_mul (τ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 K) K) (l : L) :
    actFin K L τ (finiteConorm (𝓞 K) K L (𝓞 L) x * algebraMap L (FiniteAdeleRing (𝓞 L) L) l) =
      finiteConorm (𝓞 K) K L (𝓞 L) x * algebraMap L (FiniteAdeleRing (𝓞 L) L) (τ l) := by
  rw [← teF_tmul, actFin_teF, oneTensor_tmul, teF_tmul]

private theorem finiteAdele_induction {p : FiniteAdeleRing (𝓞 L) L → Prop} (h0 : p 0)
    (hgen : ∀ (x : FiniteAdeleRing (𝓞 K) K) (l : L),
      p (finiteConorm (𝓞 K) K L (𝓞 L) x * algebraMap L (FiniteAdeleRing (𝓞 L) L) l))
    (hadd : ∀ y y', p y → p y' → p (y + y')) (y : FiniteAdeleRing (𝓞 L) L) : p y := by
  obtain ⟨t, rfl⟩ := (teF K L).surjective y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact h0
  | tmul x l => rw [teF_tmul]; exact hgen x l
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

private abbrev congrA (τ : L ≃ₐ[K] L) :
    ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] ((AdeleRing (𝓞 K) K) ⊗[K] L) :=
  Algebra.TensorProduct.congr AlgEquiv.refl τ

omit [NumberField L] in
private theorem congrA_tmul (τ : L ≃ₐ[K] L) (p : AdeleRing (𝓞 K) K) (l : L) :
    congrA K L τ (p ⊗ₜ l) = p ⊗ₜ τ l := by
  show (Algebra.TensorProduct.congr AlgEquiv.refl τ) (p ⊗ₜ l) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

private theorem genuineTensorEquiv_snd (z : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    (letI := (genuineβ K L).toAlgebra; (genuineTensorEquiv K L z).2) =
      teF K L ((prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L z).2) := rfl

omit [NumberField L] in
private theorem prodTensorAlgEquiv_snd_congrA (τ : L ≃ₐ[K] L) (y : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L (congrA K L τ y)).2 =
      oneTensor K L τ (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L y).2 := by

  have h0 : (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L)
      (0 : (AdeleRing (𝓞 K) K) ⊗[K] L) = 0 := map_zero _
  have hadd' : ∀ c d : (AdeleRing (𝓞 K) K) ⊗[K] L,
      (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L) (c + d) =
        (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L) c +
          (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L) d := fun c d => map_add _ c d
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, h0, Prod.snd_zero, map_zero]
  | tmul p l =>
    rw [congrA_tmul]
    exact (congrArg Prod.snd (prodTensorAlgEquiv_tmul K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L p (τ l))).trans
      (congrArg (fun q : ((InfiniteAdeleRing K) ⊗[K] L) × ((FiniteAdeleRing (𝓞 K) K) ⊗[K] L) => oneTensor K L τ q.2)
        (prodTensorAlgEquiv_tmul K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L p l)).symm
  | add a b ha hb => rw [map_add, hadd', hadd', Prod.snd_add, Prod.snd_add, ha, hb, map_add]

private theorem snd_genuineAct (τ : L ≃ₐ[K] L) (z : AdeleRing (𝓞 L) L) :
    ((genuineDescentDatum K L).act τ z).2 = actFin K L τ z.2 := by
  letI := (genuineβ K L).toAlgebra
  rw [genuineDescentDatum_act]
  show (genuineTensorEquiv K L (congrA K L τ ((genuineTensorEquiv K L).symm z))).2 = _

  have hS : (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L
      ((genuineTensorEquiv K L).symm z)).2 = (teF K L).symm z.2 := by
    have h := (prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L).toRingEquiv.apply_symm_apply
      ((RingEquiv.prodCongr (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv
        (teF K L)).symm z)
    exact congrArg Prod.snd h
  rw [genuineTensorEquiv_snd, prodTensorAlgEquiv_snd_congrA, hS]
  rfl

end ActFin

section Fibre

variable (v : HeightOneSpectrum (𝓞 K))

private scoped instance instFintypeOver : Fintype {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} :=
  Extension.fintype (𝓞 K) K L (𝓞 L) v

private abbrev Fib : Type _ := Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}, w.1.adicCompletion L

private abbrev OBox : Type _ := Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}, ↥(w.1.adicCompletionIntegers L)

private scoped instance instIsScalarTowerKL (w : HeightOneSpectrum (𝓞 L)) : IsScalarTower K L (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance instIsScalarTowerKKv (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    IsScalarTower K (v.adicCompletion K) (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun k =>
    ((Extension.adicCompletionSemialgHom K L (w : v.Extension (𝓞 L))).commutes k).symm

private def teHom : (v.adicCompletion K) ⊗[K] L →ₐ[v.adicCompletion K] Fib K L v :=
  Algebra.TensorProduct.lift (Algebra.ofId (v.adicCompletion K) (Fib K L v))
    (IsScalarTower.toAlgHom K L (Fib K L v)) fun _ _ => Commute.all _ _

private theorem teHom_tmul (x : v.adicCompletion K) (l : L) :
    teHom K L v (x ⊗ₜ l) = algebraMap (v.adicCompletion K) (Fib K L v) x * algebraMap L (Fib K L v) l :=
  Algebra.TensorProduct.lift_tmul _ _ _ x l

private theorem teHom_eq_baseChange_comm (z : (v.adicCompletion K) ⊗[K] L) :
    teHom K L v z = adicCompletion.baseChange K L (𝓞 L) v (Algebra.TensorProduct.comm K (v.adicCompletion K) L z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul x l =>
    rw [teHom_tmul, Algebra.TensorProduct.comm_tmul]
    funext w
    rw [adicCompletion.baseChange_tmul_apply, Pi.mul_apply, mul_comm]
    rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]; rfl

private theorem teHom_bijective : Function.Bijective (teHom K L v) := by
  have h : (teHom K L v : (v.adicCompletion K) ⊗[K] L → Fib K L v) =
      adicCompletion.baseChange K L (𝓞 L) v ∘ Algebra.TensorProduct.comm K (v.adicCompletion K) L :=
    funext (teHom_eq_baseChange_comm K L v)
  rw [h]
  exact (adicCompletion.baseChange_bijective K L (𝓞 L) v).comp (Algebra.TensorProduct.comm K _ L).bijective

private def teV : (v.adicCompletion K) ⊗[K] L ≃ₐ[v.adicCompletion K] Fib K L v :=
  AlgEquiv.ofBijective (teHom K L v) (teHom_bijective K L v)

private theorem teV_apply (z : (v.adicCompletion K) ⊗[K] L) : teV K L v z = teHom K L v z := rfl

private theorem teV_one_tmul (l : L) : teV K L v (1 ⊗ₜ l) = algebraMap L (Fib K L v) l := by
  rw [teV_apply, teHom_tmul, map_one, one_mul]

private theorem teV_tmul_one (x : v.adicCompletion K) : teV K L v (x ⊗ₜ (1 : L)) = algebraMap (v.adicCompletion K) (Fib K L v) x := by
  rw [teV_apply, teHom_tmul, map_one, mul_one]

private theorem algebraMap_L_apply (l : L) (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    algebraMap L (Fib K L v) l w = (l : w.1.adicCompletion L) := rfl

private abbrev congrV (σ : L ≃ₐ[K] L) :
    ((v.adicCompletion K) ⊗[K] L) ≃ₐ[v.adicCompletion K] ((v.adicCompletion K) ⊗[K] L) :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

omit [NumberField L] in
private theorem congrV_tmul (σ : L ≃ₐ[K] L) (x : v.adicCompletion K) (l : L) :
    congrV K L v σ (x ⊗ₜ l) = x ⊗ₜ σ l := by
  show (Algebra.TensorProduct.congr AlgEquiv.refl σ) (x ⊗ₜ l) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

private def rhoV (σ : L ≃ₐ[K] L) : Fib K L v ≃ₐ[v.adicCompletion K] Fib K L v :=
  (teV K L v).symm.trans ((congrV K L v σ).trans (teV K L v))

private theorem rhoV_apply (σ : L ≃ₐ[K] L) (c : Fib K L v) :
    rhoV K L v σ c = teV K L v (congrV K L v σ ((teV K L v).symm c)) := rfl

private theorem rhoV_teV (σ : L ≃ₐ[K] L) (z : (v.adicCompletion K) ⊗[K] L) :
    rhoV K L v σ (teV K L v z) = teV K L v (congrV K L v σ z) := by
  rw [rhoV_apply, AlgEquiv.symm_apply_apply]

private theorem rhoV_algebraMap_L (σ : L ≃ₐ[K] L) (l : L) :
    rhoV K L v σ (algebraMap L (Fib K L v) l) = algebraMap L (Fib K L v) (σ l) := by
  rw [← teV_one_tmul, rhoV_teV, congrV_tmul, teV_one_tmul]

private def piV : FiniteAdeleRing (𝓞 L) L →+* Fib K L v where
  toFun y w := y w.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem piV_apply (y : FiniteAdeleRing (𝓞 L) L) (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    piV K L v y w = y w.1 := rfl

private theorem piV_finiteConorm (x : FiniteAdeleRing (𝓞 K) K) :
    piV K L v (finiteConorm (𝓞 K) K L (𝓞 L) x) = algebraMap (v.adicCompletion K) (Fib K L v) (x v) := by
  funext w
  obtain ⟨w, rfl⟩ := w
  rfl

private theorem piV_algebraMap (l : L) : piV K L v (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) = algebraMap L (Fib K L v) l := by
  funext w
  rw [piV_apply, algebraMap_L_apply, FiniteAdeleRing.algebraMap_apply]

private theorem piV_actFin (τ : L ≃ₐ[K] L) (y : FiniteAdeleRing (𝓞 L) L) :
    piV K L v (actFin K L τ y) = rhoV K L v τ (piV K L v y) := by
  induction y using finiteAdele_induction K L with
  | h0 => rw [map_zero, map_zero, map_zero]
  | hgen x l =>
    rw [actFin_conorm_mul, map_mul, map_mul, piV_finiteConorm, piV_algebraMap, piV_algebraMap, map_mul,
      AlgEquiv.commutes, rhoV_algebraMap_L]
  | hadd y y' hy hy' => simp only [map_add, hy, hy']

private def toFib : OBox K L v →+* Fib K L v where
  toFun b w := ((b w : ↥(w.1.adicCompletionIntegers L)) : w.1.adicCompletion L)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem toFib_apply (b : OBox K L v) (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    toFib K L v b w = ((b w : ↥(w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) := rfl

private theorem toFib_injective : Function.Injective (toFib K L v) := fun _ _ h =>
  funext fun w => Subtype.ext (congrFun h w)

end Fibre

section Box

variable (v : HeightOneSpectrum (𝓞 K))

private def boxUnitOf (c : Fib K L v) (hc : ∀ w, Valued.v (c w) = 1) : (OBox K L v)ˣ where
  val w := ⟨c w, (mem_adicCompletionIntegers _ _ _).mpr (le_of_eq (hc w))⟩
  inv w := ⟨(c w)⁻¹, (mem_adicCompletionIntegers _ _ _).mpr (le_of_eq (by rw [map_inv₀, hc w, inv_one]))⟩
  val_inv := by
    funext w
    apply Subtype.ext
    have h0 : c w ≠ 0 := fun h => by
      have h1 := hc w
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    show c w * (c w)⁻¹ = 1
    rw [mul_inv_cancel₀ h0]
  inv_val := by
    funext w
    apply Subtype.ext
    have h0 : c w ≠ 0 := fun h => by
      have h1 := hc w
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    show (c w)⁻¹ * c w = 1
    rw [inv_mul_cancel₀ h0]

private theorem toFib_boxUnitOf (c : Fib K L v) (hc : ∀ w, Valued.v (c w) = 1) :
    toFib K L v (boxUnitOf K L v c hc : OBox K L v) = c := rfl

private theorem v_box_unit (b : (OBox K L v)ˣ) (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Valued.v (((b : OBox K L v) w : w.1.adicCompletion L)) = 1 :=
  adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
    ((Units.map (Pi.evalMonoidHom (fun w' : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} =>
      ↥(w'.1.adicCompletionIntegers L)) w) b).isUnit)

private def boxAut (ρ : Fib K L v ≃+* Fib K L v)
    (h1 : ∀ b : (OBox K L v)ˣ, ∀ w, Valued.v (ρ (toFib K L v (b : OBox K L v)) w) = 1)
    (h2 : ∀ b : (OBox K L v)ˣ, ∀ w, Valued.v (ρ.symm (toFib K L v (b : OBox K L v)) w) = 1) :
    (OBox K L v)ˣ ≃* (OBox K L v)ˣ where
  toFun b := boxUnitOf K L v (ρ (toFib K L v (b : OBox K L v))) (h1 b)
  invFun b := boxUnitOf K L v (ρ.symm (toFib K L v (b : OBox K L v))) (h2 b)
  left_inv b := by
    apply Units.ext
    apply toFib_injective K L v
    exact ρ.symm_apply_apply (toFib K L v (b : OBox K L v))
  right_inv b := by
    apply Units.ext
    apply toFib_injective K L v
    exact ρ.apply_symm_apply (toFib K L v (b : OBox K L v))
  map_mul' b b' := by
    apply Units.ext
    apply toFib_injective K L v
    exact map_mul ρ (toFib K L v (b : OBox K L v)) (toFib K L v (b' : OBox K L v))

private theorem toFib_boxAut_apply (ρ : Fib K L v ≃+* Fib K L v)
    (h1 : ∀ b : (OBox K L v)ˣ, ∀ w, Valued.v (ρ (toFib K L v (b : OBox K L v)) w) = 1)
    (h2 : ∀ b : (OBox K L v)ˣ, ∀ w, Valued.v (ρ.symm (toFib K L v (b : OBox K L v)) w) = 1)
    (b : (OBox K L v)ˣ) :
    toFib K L v (boxAut K L v ρ h1 h2 b : OBox K L v) = ρ (toFib K L v (b : OBox K L v)) := rfl

private theorem coe_boxAut_apply (ρ : Fib K L v ≃+* Fib K L v)
    (h1 : ∀ b : (OBox K L v)ˣ, ∀ w, Valued.v (ρ (toFib K L v (b : OBox K L v)) w) = 1)
    (h2 : ∀ b : (OBox K L v)ˣ, ∀ w, Valued.v (ρ.symm (toFib K L v (b : OBox K L v)) w) = 1)
    (b : (OBox K L v)ˣ) (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    (((boxAut K L v ρ h1 h2 b : OBox K L v) w : ↥(w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) =
      ρ (toFib K L v (b : OBox K L v)) w := rfl

end Box

section Decomposition

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)

private def MemPin : Prop :=
  ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, x ∈ U ↔
    ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      Valued.v ((x : FiniteAdeleRing (𝓞 L) L) w) = 1

private abbrev Target : Type _ :=
  (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}, (Fib K L v.1)ˣ) ×
    (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (OBox K L v.1)ˣ)

variable {K L S U}

private def boxElt (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 L) L)
    (hx : ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}, Valued.v (x w.1) ≤ 1) : OBox K L v :=
  fun w => ⟨x w.1, (mem_adicCompletionIntegers _ _ _).mpr (hx w)⟩

private theorem v_eq_one_of_mem (hU : MemPin K L S U) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (x : ↥U)
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Valued.v (((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w.1) = 1 :=
  (hU x.1).mp x.2 w.1 (by rw [w.2]; exact hv)

private theorem v_le_one_of_mem (hU : MemPin K L S U) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (x : ↥U)
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Valued.v (((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w.1) ≤ 1 :=
  le_of_eq (v_eq_one_of_mem hU hv x w)

variable (K L S U)

private def boxOf (hU : MemPin K L S U) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (x : ↥U) : (OBox K L v.1)ˣ where
  val := boxElt v.1 ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) (v_le_one_of_mem hU v.2 x)
  inv := boxElt v.1 (((x⁻¹ : ↥U) : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) (v_le_one_of_mem hU v.2 x⁻¹)
  val_inv := by
    funext w
    apply Subtype.ext
    show ((↑(x : (FiniteAdeleRing (𝓞 L) L)ˣ) * ↑((x : (FiniteAdeleRing (𝓞 L) L)ˣ)⁻¹) : FiniteAdeleRing (𝓞 L) L) w.1) = 1
    rw [Units.mul_inv]
    rfl
  inv_val := by
    funext w
    apply Subtype.ext
    show ((↑((x : (FiniteAdeleRing (𝓞 L) L)ˣ)⁻¹) * ↑(x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w.1) = 1
    rw [Units.inv_mul]
    rfl

private theorem coe_boxOf_apply (hU : MemPin K L S U) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (x : ↥U)
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}) :
    (((boxOf K L S U hU v x : (OBox K L v.1)ˣ) : OBox K L v.1) w : w.1.adicCompletion L) =
      ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w.1 := rfl

private theorem toFib_boxOf (hU : MemPin K L S U) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (x : ↥U) :
    toFib K L v.1 (boxOf K L S U hU v x : (OBox K L v.1)ˣ) =
      piV K L v.1 ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) := rfl

private def fibOf (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (x : ↥U) : (Fib K L v.1)ˣ :=
  Units.map (piV K L v.1 : FiniteAdeleRing (𝓞 L) L →* Fib K L v.1) (x : (FiniteAdeleRing (𝓞 L) L)ˣ)

private theorem coe_fibOf (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (x : ↥U) :
    ((fibOf K L S U v x : (Fib K L v.1)ˣ) : Fib K L v.1) =
      piV K L v.1 ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) := rfl

private def decomp (hU : MemPin K L S U) : ↥U →* Target K L S where
  toFun x := (fun v => fibOf K L S U v x, fun v => boxOf K L S U hU v x)
  map_one' := by
    refine Prod.ext (funext fun v => Units.ext ?_) (funext fun v => Units.ext (funext fun w => Subtype.ext ?_))
    · show piV K L v.1 (1 : FiniteAdeleRing (𝓞 L) L) = 1
      exact map_one _
    · rfl
  map_mul' x x' := by
    refine Prod.ext (funext fun v => Units.ext ?_) (funext fun v => Units.ext (funext fun w => Subtype.ext ?_))
    · show piV K L v.1 ((↑(x : (FiniteAdeleRing (𝓞 L) L)ˣ) * ↑(x' : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)) = _
      rw [map_mul]
      rfl
    · rfl

private theorem decomp_fst (hU : MemPin K L S U) (x : ↥U) (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) :
    (decomp K L S U hU x).1 v = fibOf K L S U v x := rfl

private theorem decomp_snd (hU : MemPin K L S U) (x : ↥U) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (decomp K L S U hU x).2 v = boxOf K L S U hU v x := rfl

private theorem decomp_injective (hU : MemPin K L S U) : Function.Injective (decomp K L S U hU) := by
  intro x x' h
  apply Subtype.ext
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro w
  by_cases hw : w.under (𝓞 K) ∈ S
  · have h1 := congrArg (fun z : Target K L S => ((z.1 ⟨w.under (𝓞 K), hw⟩ : (Fib K L (w.under (𝓞 K)))ˣ) :
      Fib K L (w.under (𝓞 K))) ⟨w, rfl⟩) h
    exact h1
  · have h2 := congrArg (fun z : Target K L S => (((z.2 ⟨w.under (𝓞 K), hw⟩ : (OBox K L (w.under (𝓞 K)))ˣ) :
      OBox K L (w.under (𝓞 K))) ⟨w, rfl⟩ : w.adicCompletion L)) h
    exact h2

private theorem finite_over : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}.Finite :=
  Set.Finite.subset (S.finite_toSet.biUnion fun v _ =>
      Set.finite_range (fun e : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} => (e.1 : HeightOneSpectrum (𝓞 L))))
    (fun w hw => Set.mem_biUnion hw ⟨⟨w, rfl⟩, rfl⟩)

variable {K L S} in
open scoped Classical in

private def glueFam (z : Target K L S) (w : HeightOneSpectrum (𝓞 L)) : w.adicCompletion L :=
  if h : w.under (𝓞 K) ∈ S then ((z.1 ⟨w.under (𝓞 K), h⟩ : (Fib K L (w.under (𝓞 K)))ˣ) : Fib K L (w.under (𝓞 K))) ⟨w, rfl⟩
  else (((z.2 ⟨w.under (𝓞 K), h⟩ : (OBox K L (w.under (𝓞 K)))ˣ) : OBox K L (w.under (𝓞 K))) ⟨w, rfl⟩ : w.adicCompletion L)

open scoped Classical in
private theorem glue_of_mem (z : Target K L S) (w : HeightOneSpectrum (𝓞 L)) (h : w.under (𝓞 K) ∈ S) :
    glueFam z w = ((z.1 ⟨w.under (𝓞 K), h⟩ : (Fib K L (w.under (𝓞 K)))ˣ) : Fib K L (w.under (𝓞 K))) ⟨w, rfl⟩ := by
  unfold glueFam
  rw [dif_pos h]

open scoped Classical in
private theorem glue_of_not_mem (z : Target K L S) (w : HeightOneSpectrum (𝓞 L)) (h : w.under (𝓞 K) ∉ S) :
    glueFam z w = (((z.2 ⟨w.under (𝓞 K), h⟩ : (OBox K L (w.under (𝓞 K)))ˣ) : OBox K L (w.under (𝓞 K))) ⟨w, rfl⟩ : w.adicCompletion L) := by
  unfold glueFam
  rw [dif_neg h]

private theorem glue_eq_fst (z : Target K L S) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.under (𝓞 K) = v) : glueFam z w = ((z.1 ⟨v, hv⟩ : (Fib K L v)ˣ) : Fib K L v) ⟨w, hw⟩ := by
  subst hw
  exact glue_of_mem K L S z w hv

private theorem glue_eq_snd (z : Target K L S) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.under (𝓞 K) = v) : glueFam z w = ((((z.2 ⟨v, hv⟩ : (OBox K L v)ˣ) : OBox K L v) ⟨w, hw⟩ : w.adicCompletion L)) := by
  subst hw
  exact glue_of_not_mem K L S z w hv

private theorem fib_unit_ne_zero (v : HeightOneSpectrum (𝓞 K)) (a : (Fib K L v)ˣ) (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    (a : Fib K L v) w ≠ 0 :=
  (Units.map (Pi.evalMonoidHom (fun w' : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} => w'.1.adicCompletion L) w) a).ne_zero

private theorem glue_mem_integers (z : Target K L S) (w : HeightOneSpectrum (𝓞 L)) (h : w.under (𝓞 K) ∉ S) :
    glueFam z w ∈ w.adicCompletionIntegers L := by
  rw [glue_of_not_mem K L S z w h]
  exact (((z.2 ⟨w.under (𝓞 K), h⟩ : (OBox K L (w.under (𝓞 K)))ˣ) : OBox K L (w.under (𝓞 K))) ⟨w, rfl⟩).2

private def glueAdele (z : Target K L S) : FiniteAdeleRing (𝓞 L) L :=
  ⟨glueFam z, Filter.eventually_cofinite.mpr ((finite_over K L S).subset fun w hw => by
    by_contra h
    exact hw (glue_mem_integers K L S z w h))⟩

private theorem glueAdele_apply (z : Target K L S) (w : HeightOneSpectrum (𝓞 L)) : glueAdele K L S z w = glueFam z w := rfl

private theorem v_glueAdele_of_not_mem (z : Target K L S) (w : HeightOneSpectrum (𝓞 L)) (h : w.under (𝓞 K) ∉ S) :
    Valued.v (glueAdele K L S z w) = 1 := by
  rw [glueAdele_apply, glue_of_not_mem K L S z w h]
  exact v_box_unit K L _ _ ⟨w, rfl⟩

private theorem isUnit_glueAdele (z : Target K L S) : IsUnit (glueAdele K L S z) := by
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun w => ?_, Filter.eventually_cofinite.mpr ((finite_over K L S).subset fun w hw => ?_)⟩
  · rw [glueAdele_apply]
    by_cases h : w.under (𝓞 K) ∈ S
    · rw [glue_of_mem K L S z w h]
      exact fib_unit_ne_zero K L _ _ ⟨w, rfl⟩
    · rw [glue_of_not_mem K L S z w h]
      intro h0
      have h1 := v_box_unit K L _ (z.2 ⟨w.under (𝓞 K), h⟩) ⟨w, rfl⟩
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
  · by_contra h
    exact hw (v_glueAdele_of_not_mem K L S z w h)

private def glueU (hU : MemPin K L S U) (z : Target K L S) : ↥U :=
  ⟨(isUnit_glueAdele K L S z).unit, (hU _).mpr fun w hw => v_glueAdele_of_not_mem K L S z w hw⟩

private theorem coe_glueU_apply (hU : MemPin K L S U) (z : Target K L S) (w : HeightOneSpectrum (𝓞 L)) :
    (((glueU K L S U hU z : ↥U) : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w = glueFam z w := rfl

private theorem decomp_glueU (hU : MemPin K L S U) (z : Target K L S) : decomp K L S U hU (glueU K L S U hU z) = z := by
  refine Prod.ext (funext ?_) (funext ?_)
  · rintro ⟨v, hv⟩
    apply Units.ext
    funext w'
    exact glue_eq_fst K L S z hv w'.1 w'.2
  · rintro ⟨v, hv⟩
    apply Units.ext
    funext w'
    apply Subtype.ext
    exact glue_eq_snd K L S z hv w'.1 w'.2

private def decompEquiv (hU : MemPin K L S U) : ↥U ≃* Target K L S where
  toFun := decomp K L S U hU
  invFun := glueU K L S U hU
  left_inv x := decomp_injective K L S U hU (decomp_glueU K L S U hU (decomp K L S U hU x))
  right_inv z := decomp_glueU K L S U hU z
  map_mul' := map_mul (decomp K L S U hU)

private theorem decompEquiv_apply (hU : MemPin K L S U) (x : ↥U) : decompEquiv K L S U hU x = decomp K L S U hU x := rfl

private theorem decompEquiv_symm_apply (hU : MemPin K L S U) (z : Target K L S) :
    (decompEquiv K L S U hU).symm z = glueU K L S U hU z := rfl

end Decomposition

section Dock

private theorem snd_genuineAct_pair (σ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 L) L) :
    ((genuineDescentDatum K L).act σ ((1 : InfiniteAdeleRing L), x)).2 = actFin K L σ x :=
  snd_genuineAct K L σ _

private def PhiF (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))) (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) :
    (Fib K L v.1)ˣ ≃* (Fib K L v.1)ˣ :=
  Units.mapEquiv (rhoV K L v.1 σ).toMulEquiv

private theorem coe_PhiF (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))) (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
    (u : (Fib K L v.1)ˣ) :
    ((PhiF K L σ S v u : (Fib K L v.1)ˣ) : Fib K L v.1) = rhoV K L v.1 σ (u : Fib K L v.1) := rfl

private theorem hPhiF (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))) (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
    (u : (Fib K L v.1)ˣ) (x : FiniteAdeleRing (𝓞 L) L)
    (hx : ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, x w.1 = (u : Fib K L v.1) w)
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}) :
    ((genuineDescentDatum K L).act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 = (PhiF K L σ S v u : Fib K L v.1) w := by
  rw [snd_genuineAct_pair, coe_PhiF]
  have hu : piV K L v.1 x = (u : Fib K L v.1) := funext hx
  show piV K L v.1 (actFin K L σ x) w = _
  rw [piV_actFin, hu]

private theorem piV_Phi (σ : L ≃ₐ[K] L) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (x : ↥U) (v : HeightOneSpectrum (𝓞 K)) :
    piV K L v ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      rhoV K L v σ (piV K L v ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)) := by
  rw [← hΦ x, piV_actFin]

private theorem toFib_eq_piV_glue (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (b : (OBox K L v.1)ˣ)
    (z : Target K L S) (hzb : z.2 v = b) :
    toFib K L v.1 (b : OBox K L v.1) =
      piV K L v.1 (((glueU K L S U hU z : ↥U) : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) := by
  have h2 : (decomp K L S U hU (glueU K L S U hU z)).2 v = b := by rw [decomp_glueU]; exact hzb
  rw [← toFib_boxOf K L S U hU v, ← decomp_snd, h2]

open scoped Classical in

private def single (S : Finset (HeightOneSpectrum (𝓞 K))) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (b : (OBox K L v.1)ˣ) :
    Target K L S :=
  (1, Pi.mulSingle v b)

open scoped Classical in
private theorem single_snd_self (S : Finset (HeightOneSpectrum (𝓞 K))) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (b : (OBox K L v.1)ˣ) : (single K L S v b).2 v = b :=
  Pi.mulSingle_eq_same (M := fun v' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => (OBox K L v'.1)ˣ) v b

private theorem box_h1 (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (b : (OBox K L v.1)ˣ)
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}) :
    Valued.v (((rhoV K L v.1 σ).toRingEquiv) (toFib K L v.1 (b : OBox K L v.1)) w) = 1 := by
  have hz := toFib_eq_piV_glue K L S U hU v b (single K L S v b) (single_snd_self K L S v b)
  rw [show ((rhoV K L v.1 σ).toRingEquiv) (toFib K L v.1 (b : OBox K L v.1)) =
      rhoV K L v.1 σ (toFib K L v.1 (b : OBox K L v.1)) from rfl, hz, ← piV_Phi K L σ U Φ hΦ, piV_apply]
  exact v_eq_one_of_mem hU v.2 _ w

private theorem box_h2 (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (b : (OBox K L v.1)ˣ)
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}) :
    Valued.v (((rhoV K L v.1 σ).toRingEquiv).symm (toFib K L v.1 (b : OBox K L v.1)) w) = 1 := by
  have hz := toFib_eq_piV_glue K L S U hU v b (single K L S v b) (single_snd_self K L S v b)
  have hx : piV K L v.1 (((glueU K L S U hU (single K L S v b) : ↥U) : (FiniteAdeleRing (𝓞 L) L)ˣ) :
      FiniteAdeleRing (𝓞 L) L) =
      rhoV K L v.1 σ (piV K L v.1 (((Φ.symm (glueU K L S U hU (single K L S v b)) : ↥U) :
        (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)) := by
    rw [← piV_Phi K L σ U Φ hΦ, MulEquiv.apply_symm_apply]
  have hkey : ((rhoV K L v.1 σ).toRingEquiv).symm (toFib K L v.1 (b : OBox K L v.1)) =
      piV K L v.1 (((Φ.symm (glueU K L S U hU (single K L S v b)) : ↥U) :
        (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) := by
    rw [hz, hx]
    exact (rhoV K L v.1 σ).toRingEquiv.symm_apply_apply _
  rw [hkey, piV_apply]
  exact v_eq_one_of_mem hU v.2 _ w

private def PhiB (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) : (OBox K L v.1)ˣ ≃* (OBox K L v.1)ˣ :=
  boxAut K L v.1 (rhoV K L v.1 σ).toRingEquiv (box_h1 K L σ S U hU Φ hΦ v) (box_h2 K L σ S U hU Φ hΦ v)

private theorem coe_PhiB_apply (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (b : (OBox K L v.1)ˣ)
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}) :
    (((PhiB K L σ S U hU Φ hΦ v b : OBox K L v.1) w : ↥(w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) =
      rhoV K L v.1 σ (toFib K L v.1 (b : OBox K L v.1)) w := rfl

private theorem hPhiB (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (OBox K L v.1)ˣ) (x : FiniteAdeleRing (𝓞 L) L)
    (hx : ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
      x w.1 = (((u : OBox K L v.1) w : ↥(w.1.adicCompletionIntegers L)) : w.1.adicCompletion L))
    (w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}) :
    ((genuineDescentDatum K L).act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
      (((PhiB K L σ S U hU Φ hΦ v u : OBox K L v.1) w : ↥(w.1.adicCompletionIntegers L)) : w.1.adicCompletion L) := by
  rw [snd_genuineAct_pair, coe_PhiB_apply]
  have hu : piV K L v.1 x = toFib K L v.1 (u : OBox K L v.1) := funext hx
  show piV K L v.1 (actFin K L σ x) w = _
  rw [piV_actFin, hu]

private def pairAct (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (z : Target K L S) : Target K L S :=
  (fun v => PhiF K L σ S v (z.1 v), fun v => PhiB K L σ S U hU Φ hΦ v (z.2 v))

private theorem decomp_Phi (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (x : ↥U) :
    decompEquiv K L S U hU (Φ x) = pairAct K L σ S U hU Φ hΦ (decompEquiv K L S U hU x) := by
  refine Prod.ext (funext fun v => Units.ext ?_) (funext fun v => Units.ext (funext fun w => Subtype.ext ?_))
  · show piV K L v.1 ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      rhoV K L v.1 σ (piV K L v.1 ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    exact piV_Phi K L σ U Φ hΦ x v.1
  · show ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w.1 =
      rhoV K L v.1 σ (toFib K L v.1 (boxOf K L S U hU v x : OBox K L v.1)) w
    rw [toFib_boxOf, ← piV_Phi K L σ U Φ hΦ, piV_apply]

set_option maxHeartbeats 1600000 in
private theorem decomp_Phi_pow (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (i : ℕ) (x : ↥U) :
    decompEquiv K L S U hU ((Φ ^ i) x) =
      (fun v => (PhiF K L σ S v ^ i) ((decompEquiv K L S U hU x).1 v),
        fun v => (PhiB K L σ S U hU Φ hΦ v ^ i) ((decompEquiv K L S U hU x).2 v)) := by
  induction i generalizing x with
  | zero =>
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_) <;> simp only [pow_zero, MulAut.one_apply]
  | succ i ih =>
    rw [pow_succ, MulAut.mul_apply, ih (Φ x), decomp_Phi K L σ S U hU Φ hΦ]
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · show (PhiF K L σ S v ^ i) (PhiF K L σ S v ((decompEquiv K L S U hU x).1 v)) =
        (PhiF K L σ S v ^ (i + 1)) ((decompEquiv K L S U hU x).1 v)
      rw [pow_succ, MulAut.mul_apply]
    · show (PhiB K L σ S U hU Φ hΦ v ^ i) (PhiB K L σ S U hU Φ hΦ v ((decompEquiv K L S U hU x).2 v)) =
        (PhiB K L σ S U hU Φ hΦ v ^ (i + 1)) ((decompEquiv K L S U hU x).2 v)
      rw [pow_succ, MulAut.mul_apply]

private def eA (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) :
    Additive ↥U ≃+ Additive (Target K L S) :=
  MulEquiv.toAdditive (decompEquiv K L S U hU)

private theorem eA_ofMul (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (x : ↥U) :
    eA K L S U hU (Additive.ofMul x) = Additive.ofMul (decompEquiv K L S U hU x) := rfl

private theorem eA_symm_ofMul (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (z : Target K L S) :
    (eA K L S U hU).symm (Additive.ofMul z) = Additive.ofMul ((decompEquiv K L S U hU).symm z) := rfl

private def conjT (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U)
    (f : Additive ↥U →+ Additive ↥U) : Additive (Target K L S) →+ Additive (Target K L S) :=
  ((eA K L S U hU : Additive ↥U ≃+ Additive (Target K L S)) : Additive ↥U →+ Additive (Target K L S)).comp
    (f.comp ((eA K L S U hU).symm : Additive (Target K L S) →+ Additive ↥U))

private theorem conjT_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (f : Additive ↥U →+ Additive ↥U) (b : Additive (Target K L S)) :
    conjT K L S U hU f b = eA K L S U hU (f ((eA K L S U hU).symm b)) := rfl

private theorem conjT_conj (S : Finset (HeightOneSpectrum (𝓞 K))) (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : MemPin K L S U) (f : Additive ↥U →+ Additive ↥U) (a : Additive ↥U) :
    conjT K L S U hU f (eA K L S U hU a) = eA K L S U hU (f a) := by
  rw [conjT_apply, AddEquiv.symm_apply_apply]

set_option maxHeartbeats 1600000 in

private theorem conjT_d_pin (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (d : Additive ↥U →+ Additive ↥U)
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul (Φ u) - Additive.ofMul u) (u : Target K L S) :
    conjT K L S U hU d (Additive.ofMul u) =
      Additive.ofMul ((fun v => PhiF K L σ S v (u.1 v), fun v => PhiB K L σ S U hU Φ hΦ v (u.2 v)))
        - Additive.ofMul u := by
  rw [conjT_apply, eA_symm_ofMul, hd, map_sub, eA_ofMul, eA_ofMul, decomp_Phi K L σ S U hU Φ hΦ,
    MulEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 1600000 in

private theorem conjT_N_pin (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ) (hU : MemPin K L S U) (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (n : ℕ) (N : Additive ↥U →+ Additive ↥U)
    (hN : ∀ u, N (Additive.ofMul u) = ∑ i ∈ Finset.range n, Additive.ofMul ((Φ ^ i) u)) (u : Target K L S) :
    conjT K L S U hU N (Additive.ofMul u) =
      ∑ i ∈ Finset.range n,
        Additive.ofMul ((fun v => (PhiF K L σ S v ^ i) (u.1 v), fun v => (PhiB K L σ S U hU Φ hΦ v ^ i) (u.2 v))) := by
  rw [conjT_apply, eA_symm_ofMul, hN, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eA_ofMul, decomp_Phi_pow K L σ S U hU Φ hΦ, MulEquiv.apply_symm_apply]

end Dock

section Assembly

private theorem finnum_genuine
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, x ∈ U ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
        Valued.v ((x : FiniteAdeleRing (𝓞 L) L) w) = 1)
    (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U,
      ((genuineDescentDatum K L).act σ (1, ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))).2
        = ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))
    (d : Additive ↥U →+ Additive ↥U)
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul (Φ u) - Additive.ofMul u)
    (N : Additive ↥U →+ Additive ↥U)
    (hN : ∀ u, N (Additive.ofMul u)
      = ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), Additive.ofMul ((Φ ^ i) u))
    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  have hΦ' : ∀ x : ↥U, actFin K L σ ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) :=
    fun x => (snd_genuineAct_pair K L σ _).symm.trans (hΦ x)
  have hU' : MemPin K L S U := hU
  obtain ⟨h0, h1⟩ := M4aHerbrandFinnumSol.supplier_finFibreBox K L σ hσ S hSram (genuineDescentDatum K L)
    (PhiF K L σ S) (hPhiF K L σ S) (PhiB K L σ S U hU' Φ hΦ') (hPhiB K L σ S U hU' Φ hΦ')
    (conjT K L S U hU' d) (conjT_d_pin K L σ S U hU' Φ hΦ' d hd)
    (conjT K L S U hU' N) (conjT_N_pin K L σ S U hU' Φ hΦ' (Nat.card (L ≃ₐ[K] L)) N hN) sf hsf
  obtain ⟨e0, e1⟩ := tate_card_conj (eA K L S U hU') d N (conjT K L S U hU' d) (conjT K L S U hU' N)
    (conjT_conj K L S U hU' d) (conjT_conj K L S U hU' N)
  exact ⟨e0.trans h0, e1.trans h1⟩

end Assembly

end M4aHerbrandFinnumSol
p2m_reactivate "P2MW.S_M4aHerbrand_finSIdele_tateCard_eq_localDegreeProd.M4aHerbrandFinnumSol"

end
p2m_reactivate "P2MW.S_M4aHerbrand_finSIdele_tateCard_eq_localDegreeProd.M4aHerbrandFinnumSol"

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (U : Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hU : ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, x ∈ U ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
        Valued.v ((x : FiniteAdeleRing (𝓞 L) L) w) = 1)

    (Φ : ↥U ≃* ↥U)
    (hΦ : ∀ x : ↥U,
      (D.act σ (1, ((x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))).2
        = ((Φ x : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L))

    (d : Additive ↥U →+ Additive ↥U)
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul (Φ u) - Additive.ofMul u)
    (N : Additive ↥U →+ Additive ↥U)
    (hN : ∀ u, N (Additive.ofMul u)
      = ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)), Additive.ofMul ((Φ ^ i) u))

    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  haveI : Subsingleton (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  exact M4aHerbrandFinnumSol.finnum_genuine K L σ hσ S hSram U hU Φ hΦ d hd N hN sf hsf

end S_M4aHerbrand_finSIdele_tateCard_eq_localDegreeProd
end P2MW
export P2MW.S_M4aHerbrand_finSIdele_tateCard_eq_localDegreeProd (solution)
