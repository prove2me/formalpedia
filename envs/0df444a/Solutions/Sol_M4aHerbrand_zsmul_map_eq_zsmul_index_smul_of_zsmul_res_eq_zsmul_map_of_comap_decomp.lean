-- Prove2me | solution 1 for M4aHerbrand.zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/260987f7-3a8d-590d-9976-a5eed77fb34d

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_FiniteConorm
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_NumberField_PlaceTransport_transport_adicCompletionSemialgHom
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

namespace groupCohomology
p2m_export "groupCohomology" "map_comp congr cochainsFunctor map_id cochainsMap map_id_comp map cochainsMap_f π exists_corestriction_map_map_res_eq_map_norm"
namespace S2Alg
p2m_open "groupCohomology"

variable {k : Type} [CommRing k]

lemma map_eq_id_of_forall {G : Type} [Group G] (A : Rep k G) (f : G →* G) (φ : Rep.res f A ⟶ A)
    (hf : ∀ g, f g = g) (hφ : ∀ a : A, φ.hom a = a) (n : ℕ) :
    groupCohomology.map f φ n = 𝟙 _ := by
  have h : cochainsMap f φ = 𝟙 _ := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    rw [cochainsMap_f, HomologicalComplex.id_f]
    ext x v
    have hfv : (⇑f ∘ v) = v := funext fun j => hf (v j)
    simp [hfv, hφ]
  show HomologicalComplex.homologyMap (cochainsMap f φ) n = _
  rw [h, HomologicalComplex.homologyMap_id]
  rfl

lemma map_id_nsmul {G : Type} [Group G] {A B : Rep k G} (φ : A ⟶ B) (m : ℕ) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (m • φ) n = m • groupCohomology.map (MonoidHom.id G) φ n := by
  show (HomologicalComplex.homologyFunctor _ _ n).map ((cochainsFunctor k G).map (m • φ)) =
    m • (HomologicalComplex.homologyFunctor _ _ n).map ((cochainsFunctor k G).map φ)
  rw [Functor.map_nsmul, Functor.map_nsmul]

lemma nsmul_hom_apply {G : Type} [Group G] {A B : Rep k G} (f : A ⟶ B) (x : A) (m : ℕ) :
    (Rep.Hom.hom (m • f)) x = m • (Rep.Hom.hom f) x := by
  induction m with
  | zero => rw [zero_nsmul, zero_nsmul]; rfl
  | succ m ih =>
    rw [succ_nsmul, succ_nsmul, ← ih]
    rfl

section transport

variable {H D : Type} [Group H] [Group D] (S : Subgroup H) (e : D ≃* S)

noncomputable def liftHom {R C : Rep k H}
    (φ : Rep.res (S.subtype.comp e.toMonoidHom) R ⟶ Rep.res (S.subtype.comp e.toMonoidHom) C) :
    Rep.res S.subtype R ⟶ Rep.res S.subtype C :=
  Rep.ofHom ⟨φ.hom, fun s => LinearMap.ext fun x => by
    have h := Rep.hom_comm_apply φ (e.symm s) x
    change φ.hom (R.ρ (S.subtype (e (e.symm s))) x) = C.ρ (S.subtype (e (e.symm s))) (φ.hom x) at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h⟩

@[scoped simp] lemma liftHom_hom_apply {R C : Rep k H}
    (φ : Rep.res (S.subtype.comp e.toMonoidHom) R ⟶ Rep.res (S.subtype.comp e.toMonoidHom) C) (x : R) :
    (liftHom S e φ).hom x = φ.hom x := rfl

noncomputable abbrev along (X : Rep k H) (n : ℕ) :
    groupCohomology (Rep.res S.subtype X) n ⟶ groupCohomology (Rep.res (S.subtype.comp e.toMonoidHom) X) n :=
  groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom (Rep.res S.subtype X))) n

noncomputable def back (X : Rep k H) :
    Rep.res e.symm.toMonoidHom (Rep.res (S.subtype.comp e.toMonoidHom) X) ⟶ Rep.res S.subtype X :=
  Rep.ofHom ⟨LinearMap.id, fun s => LinearMap.ext fun x => by
    change X.ρ (S.subtype (e (e.symm s))) x = X.ρ (S.subtype s) x
    rw [MulEquiv.apply_symm_apply]⟩

lemma along_comp_back (X : Rep k H) (n : ℕ) :
    along S e X n ≫ groupCohomology.map e.symm.toMonoidHom (back S e X) n = 𝟙 _ := by
  rw [along, ← groupCohomology.map_comp]
  exact map_eq_id_of_forall _ _ _ (fun s => e.apply_symm_apply s) (fun _ => rfl) n

lemma along_injective (X : Rep k H) (n : ℕ) : Function.Injective (along S e X n).hom := by
  intro a b h
  have this := congrArg (groupCohomology.map e.symm.toMonoidHom (back S e X) n).hom h
  have hc := along_comp_back S e X n
  have key : ∀ x, (groupCohomology.map e.symm.toMonoidHom (back S e X) n).hom ((along S e X n).hom x) = x :=
    fun x => by
      have hx := congrArg (fun f => (ModuleCat.Hom.hom f) x) hc
      simp [ModuleCat.hom_comp] at hx
      exact hx
  exact (key a).symm.trans (this.trans (key b))

lemma map_comp_eq_along (X : Rep k H) (n : ℕ) :
    groupCohomology.map (S.subtype.comp e.toMonoidHom) (𝟙 (Rep.res (S.subtype.comp e.toMonoidHom) X)) n =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) n ≫ along S e X n := by
  rw [along, ← groupCohomology.map_comp]
  rfl

lemma along_map_liftHom {R C : Rep k H}
    (φ : Rep.res (S.subtype.comp e.toMonoidHom) R ⟶ Rep.res (S.subtype.comp e.toMonoidHom) C) (n : ℕ) :
    groupCohomology.map (MonoidHom.id ↥S) (liftHom S e φ) n ≫ along S e C n =
      along S e R n ≫ groupCohomology.map (MonoidHom.id D) φ n := by
  rw [along, along, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  congr 1

end transport

end groupCohomology.S2Alg
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "map_comp congr cochainsFunctor map_id cochainsMap map_id_comp map cochainsMap_f π exists_corestriction_map_map_res_eq_map_norm"
namespace S2Alg
p2m_open "groupCohomology"

variable {k : Type} [CommRing k]

theorem core {H D : Type} [Group H] [Group D] (S : Subgroup H) [S.FiniteIndex] [Fintype (H ⧸ S)] (e : D ≃* S)
    (R C : Rep k H)
    (φ : Rep.res (S.subtype.comp e.toMonoidHom) R ⟶ Rep.res (S.subtype.comp e.toMonoidHom) C) (Nφ : R ⟶ C)
    (hN : ∀ x : R, Nφ.hom x = ∑ g : H ⧸ S, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x)))
    (n : ℕ) (c : ℤ) (z : groupCohomology R n) (y : groupCohomology C n)
    (hy : c • (groupCohomology.map (S.subtype.comp e.toMonoidHom) (𝟙 (Rep.res (S.subtype.comp e.toMonoidHom) C)) n).hom y =
          c • (groupCohomology.map (MonoidHom.id D) φ n).hom
                ((groupCohomology.map (S.subtype.comp e.toMonoidHom) (𝟙 (Rep.res (S.subtype.comp e.toMonoidHom) R)) n).hom z)) :
    c • (groupCohomology.map (MonoidHom.id H) Nφ n).hom z = c • (S.index • y) := by
  classical
  obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_map_map_res_eq_map_norm S C n

  have hy' : c • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) n).hom y =
      c • (groupCohomology.map (MonoidHom.id ↥S) (liftHom S e φ) n).hom
            ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n).hom z) := by
    apply along_injective S e C n
    rw [map_zsmul, map_zsmul]
    have h1 := congrArg (fun f => (ModuleCat.Hom.hom f) y) (map_comp_eq_along S e C n)
    have h2 := congrArg (fun f => (ModuleCat.Hom.hom f) z) (map_comp_eq_along S e R n)
    have h3 := congrArg (fun f => (ModuleCat.Hom.hom f)
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n).hom z)) (along_map_liftHom S e φ n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2 h3
    rw [h3, ← h2, ← h1]
    exact hy

  have hproj := hcor R (liftHom S e φ) Nφ (fun x => by have h__af := hN x; simp only [liftHom_hom_apply] at h__af; exact h__af) z
  have hidx : ∀ x : C, ((Fintype.card (H ⧸ S) : ℕ) • (𝟙 C : C ⟶ C)).hom x =
      ∑ g : H ⧸ S, C.ρ g.out ((𝟙 (Rep.res S.subtype C) : _ ⟶ _).hom (C.ρ g.out⁻¹ x)) := fun x => by
    rw [nsmul_hom_apply]
    simp [Representation.self_inv_apply, Finset.sum_const, Finset.card_univ]
  have hres := hcor C (𝟙 _) ((Fintype.card (H ⧸ S) : ℕ) • 𝟙 C) hidx y
  rw [groupCohomology.map_id, map_id_nsmul, groupCohomology.map_id] at hres
  have hres' : cor ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) n).hom y) = Fintype.card (H ⧸ S) • y := by
    simpa using hres

  have e1 := congrArg cor hy'
  rw [map_zsmul, map_zsmul, hres', hproj] at e1
  rw [S.index_eq_card, Nat.card_eq_fintype_card]
  exact e1.symm

end groupCohomology.S2Alg
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

namespace groupCohomology
p2m_export "groupCohomology" "map_comp congr cochainsFunctor map_id cochainsMap map_id_comp map cochainsMap_f π exists_corestriction_map_map_res_eq_map_norm"
namespace S2Alg
p2m_open "groupCohomology"

theorem zsmul_map_norm_eq_zsmul_index_zsmul_of_zsmul_map_eq
    {k H D : Type} [CommRing k] [Group H] [Group D]
    (i : D →* H) (hi : Function.Injective i) [i.range.FiniteIndex] [Fintype (H ⧸ i.range)]
    (R C : Rep k H) (φ : Rep.res i R ⟶ Rep.res i C) (Nφ : R ⟶ C)
    (hN : ∀ x : R, Nφ.hom x = ∑ g : H ⧸ i.range, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x)))
    (n : ℕ) (c : ℤ) (z : groupCohomology R n) (y : groupCohomology C n)
    (hy : c • (groupCohomology.map i (𝟙 (Rep.res i C)) n).hom y =
          c • (groupCohomology.map (MonoidHom.id D) φ n).hom ((groupCohomology.map i (𝟙 (Rep.res i R)) n).hom z)) :
    c • (groupCohomology.map (MonoidHom.id H) Nφ n).hom z = c • (i.range.index • y) :=
  core i.range (MonoidHom.ofInjective hi) R C φ Nφ hN n c z y hy

end groupCohomology.S2Alg
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

namespace groupCohomology
p2m_export "groupCohomology" "map_comp congr cochainsFunctor map_id cochainsMap map_id_comp map cochainsMap_f π exists_corestriction_map_map_res_eq_map_norm"
namespace S2Alg
p2m_open "groupCohomology"

variable {k : Type} [CommRing k]

lemma map_res_res_apply {Q H D : Type} [Group Q] [Group H] [Group D] (f : H →* Q) (g : D →* H) (X : Rep k Q) (n : ℕ)
    (z : groupCohomology X n) :
    (groupCohomology.map g (𝟙 (Rep.res g (Rep.res f X))) n).hom ((groupCohomology.map f (𝟙 (Rep.res f X)) n).hom z) =
      (groupCohomology.map (f.comp g) (𝟙 (Rep.res (f.comp g) X)) n).hom z := by
  have h : groupCohomology.map (f.comp g) (𝟙 (Rep.res (f.comp g) X)) n =
      groupCohomology.map f (𝟙 (Rep.res f X)) n ≫ groupCohomology.map g (𝟙 (Rep.res g (Rep.res f X))) n := by
    rw [← groupCohomology.map_comp]
    rfl
  have h' := congrArg (fun φ => (ModuleCat.Hom.hom φ) z) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'.symm

lemma map_eq_res_comp_map_id {Q D : Type} [Group Q] [Group D] (f : D →* Q) (X : Rep k Q) {B : Rep k D}
    (ψ : Rep.res f X ⟶ B) (n : ℕ) :
    groupCohomology.map f ψ n =
      groupCohomology.map f (𝟙 (Rep.res f X)) n ≫ groupCohomology.map (MonoidHom.id D) (A := Rep.res f X) ψ n := by
  rw [← groupCohomology.map_comp]
  rfl

lemma map_eq_res_comp_map_id_apply {Q D : Type} [Group Q] [Group D] (f : D →* Q) (X : Rep k Q) {B : Rep k D}
    (ψ : Rep.res f X ⟶ B) (n : ℕ) (z : groupCohomology X n) :
    (groupCohomology.map f ψ n).hom z =
      (groupCohomology.map (MonoidHom.id D) (A := Rep.res f X) ψ n).hom ((groupCohomology.map f (𝟙 (Rep.res f X)) n).hom z) := by
  have h' := congrArg (fun φ => (ModuleCat.Hom.hom φ) z) (map_eq_res_comp_map_id f X ψ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'

theorem glue {Q H D : Type} [Group Q] [Group H] [Group D]
    (πH : H →* Q) (i : D →* H) (hi : Function.Injective i) [i.range.FiniteIndex] [Fintype (H ⧸ i.range)]
    (M : Rep k Q) (C : Rep k H) (B : Rep k D)
    (iW : Rep.res (πH.comp i) M ⟶ B) (φW : B ⟶ Rep.res i C) (κ : Rep.res πH M ⟶ C)
    (hN : ∀ x : Rep.res πH M, κ.hom x = ∑ g : H ⧸ i.range, C.ρ g.out (φW.hom (iW.hom ((Rep.res πH M).ρ g.out⁻¹ x))))
    (n : ℕ) (c : ℤ) (z : groupCohomology M n) (y : groupCohomology C n)
    (hy : c • (groupCohomology.map i (𝟙 (Rep.res i C)) n).hom y =
          c • (groupCohomology.map (MonoidHom.id D) (A := B) φW n).hom ((groupCohomology.map (πH.comp i) iW n).hom z)) :
    c • (groupCohomology.map πH κ n).hom z = c • (i.range.index • y) := by
  have hA := map_res_res_apply πH i M n z
  have hC := map_eq_res_comp_map_id_apply (πH.comp i) M iW n z
  have hB := groupCohomology.map_id_comp (A := Rep.res (πH.comp i) M) (B := B) (C := Rep.res i C) iW φW n
  have hD := map_eq_res_comp_map_id_apply πH M κ n z
  have key := zsmul_map_norm_eq_zsmul_index_zsmul_of_zsmul_map_eq i hi (Rep.res πH M) C (iW ≫ φW) κ
    (fun x => (hN x).trans (Finset.sum_congr rfl fun g _ => rfl)) n c
    ((groupCohomology.map πH (𝟙 (Rep.res πH M)) n).hom z) y
    (by
      rw [hA, hB]
      have hB' : ∀ v, (ModuleCat.Hom.hom (groupCohomology.map (MonoidHom.id D) (A := Rep.res (πH.comp i) M) iW n ≫
          groupCohomology.map (MonoidHom.id D) (A := B) φW n)) v =
          (groupCohomology.map (MonoidHom.id D) (A := B) φW n).hom
            ((groupCohomology.map (MonoidHom.id D) (A := Rep.res (πH.comp i) M) iW n).hom v) := fun v => by
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [hB', ← hC]
      exact hy)
  rw [hD]
  exact key

end groupCohomology.S2Alg
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_infPart_apply coe_finPart_apply principalIdeles IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ Bridge.genuineβ_fst Bridge.genuineβ_snd Bridge.finiteConorm_apply GenuineDescent.genuineDescentDatum subsingleton_ideleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum_act_fst_apply"
namespace S2Arith
p2m_open "M4aHerbrand"

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

theorem idele_ext {x y : (AdeleRing R F)ˣ} (hinf : infPart x = infPart y) (hfin : ∀ w, finPart w x = finPart w y) : x = y := by
  apply Units.ext
  refine Prod.ext (congrArg Units.val hinf) ?_
  apply FiniteAdeleRing.ext
  intro w
  exact congrArg Units.val (hfin w)

theorem coe_unitsAct {E : Type*} [Field E] [Algebra E F] (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) (u : (AdeleRing R F)ˣ) :
    ((D.unitsAct g u : (AdeleRing R F)ˣ) : AdeleRing R F) = D.act g (u : AdeleRing R F) :=
  rfl

theorem S2L1_unitsAct_concentrated
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 K), (w.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : (w.adicCompletion K)ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 K), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (y : (w.adicCompletion K)ˣ) :
    D.unitsAct σ (ι' w y) = ι' (σ • w) (NumberField.PlaceTransport.transportUnits σ rfl y) := by

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 K) E K
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum E K := Subsingleton.elim _ _
  apply M4aHerbrand.S2Arith.idele_ext
  ·
    rw [(hι' (σ • w) _).2.2]
    apply Units.ext
    rw [coe_infPart_apply, M4aHerbrand.S2Arith.coe_unitsAct]
    funext v
    rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply E K σ _ (smul_inv_smul σ v)]
    have h1 : ((ι' w y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
      rw [← coe_infPart_apply, (hι' w y).2.2]
      rfl
    rw [h1]
    change NumberField.InfinitePlaceTransport.transport σ _ 1 = 1
    exact map_one _
  · intro w''
    rcases eq_or_ne w'' (σ • w) with rfl | hne
    ·
      rw [(hι' (σ • w) _).1]
      apply Units.ext
      rw [coe_finPart_apply, M4aHerbrand.S2Arith.coe_unitsAct,
        M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E K σ _ (rfl : σ • w = σ • w),
        ← coe_finPart_apply, (hι' w y).1]
      rfl
    ·
      rw [(hι' (σ • w) _).2.1 w'' hne]
      apply Units.ext
      rw [coe_finPart_apply, M4aHerbrand.S2Arith.coe_unitsAct,
        M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E K σ _ (smul_inv_smul σ w''),
        ← coe_finPart_apply, (hι' w y).2.1 (σ⁻¹ • w'') (fun h => hne (by rw [← h, smul_inv_smul]))]
      change NumberField.PlaceTransport.transport σ _ ((1 : ((σ⁻¹ • w'').adicCompletion K)ˣ) : (σ⁻¹ • w'').adicCompletion K) = ((1 : (w''.adicCompletion K)ˣ) : w''.adicCompletion K)
      rw [Units.val_one, Units.val_one, map_one]

end M4aHerbrand.S2Arith
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_infPart_apply coe_finPart_apply principalIdeles IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ Bridge.genuineβ_fst Bridge.genuineβ_snd Bridge.finiteConorm_apply GenuineDescent.genuineDescentDatum subsingleton_ideleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum_act_fst_apply"
namespace S2Arith
p2m_open "M4aHerbrand"

section tower

variable {E F F' : Type} [Field E] [Field F] [Field F'] [NumberField F] [NumberField F']
  [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F']

omit [NumberField F] [NumberField F'] in

theorem restrictNormalHom_restrictScalars [Normal E F] (m : F' ≃ₐ[F] F') :
    AlgEquiv.restrictNormalHom F (AlgEquiv.restrictScalars E m) = 1 := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap F F').injective
  rw [show AlgEquiv.restrictNormalHom F (AlgEquiv.restrictScalars E m) = (AlgEquiv.restrictScalars E m).restrictNormal F from rfl,
    AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]

omit [NumberField F] [NumberField F'] in

theorem restrictScalars_smul_place (m : F' ≃ₐ[F] F') (W : HeightOneSpectrum (𝓞 F')) :
    (AlgEquiv.restrictScalars E m) • W = m • W := rfl

omit [NumberField F] [NumberField F'] in

theorem smul_algebraMap_ringOfIntegers [Normal E F] (σ : F' ≃ₐ[E] F') (x : 𝓞 F) :
    σ • (algebraMap (𝓞 F) (𝓞 F') x) = algebraMap (𝓞 F) (𝓞 F') ((AlgEquiv.restrictNormalHom F σ) • x) := by
  apply Subtype.ext
  change σ (algebraMap F F' (x : F)) = algebraMap F F' (((AlgEquiv.restrictNormalHom F σ) : F ≃ₐ[E] F) (x : F))
  rw [show AlgEquiv.restrictNormalHom F σ = σ.restrictNormal F from rfl, AlgEquiv.restrictNormal_commutes]

omit [NumberField F] [NumberField F'] in

theorem under_smul [Normal E F] (σ : F' ≃ₐ[E] F') (W : HeightOneSpectrum (𝓞 F')) :
    (σ • W).under (𝓞 F) = (AlgEquiv.restrictNormalHom F σ) • (W.under (𝓞 F)) := by
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, NumberField.PlaceTransport.smul_asIdeal (AlgEquiv.restrictNormalHom F σ),
    HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
    NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  change σ⁻¹ • algebraMap (𝓞 F) (𝓞 F') x ∈ W.asIdeal ↔ algebraMap (𝓞 F) (𝓞 F') ((AlgEquiv.restrictNormalHom F σ)⁻¹ • x) ∈ W.asIdeal
  rw [← map_inv, smul_algebraMap_ringOfIntegers]

variable [IsGalois E F] [IsGalois E F']

theorem exists_eq_restrictScalars_mul (W : HeightOneSpectrum (𝓞 F')) (g : F' ≃ₐ[E] F')
    (hg : AlgEquiv.restrictNormalHom F g ∈ NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) :
    ∃ (m : F' ≃ₐ[F] F') (d : F' ≃ₐ[E] F'), d ∈ NumberField.PlaceDecomp.decomp E F' W ∧
      g = AlgEquiv.restrictScalars E m * d := by
  haveI : IsGalois F F' := IsGalois.tower_top_of_isGalois E F F'
  have h1 : (g • W).under (𝓞 F) = W.under (𝓞 F) := by
    rw [under_smul]
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp] at hg
    exact hg
  have h2 : g • W ∈ MulAction.orbit (F' ≃ₐ[F] F') W := by
    rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq F F' W]; exact h1
  obtain ⟨m, hm⟩ := h2
  refine ⟨m, (AlgEquiv.restrictScalars E m)⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hm' : g • W = AlgEquiv.restrictScalars E m • W := hm.symm
  rw [← NumberField.PlaceTransport.stabilizer_eq_decomp, MulAction.mem_stabilizer_iff, mul_smul, hm', inv_smul_smul]

end tower
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

section summand

attribute [local instance 10000] Rep.hV1 Rep.hV2

variable {H D Dw : Type} [Group H] [Group D] [Group Dw] (πH : H →* Dw) (i : D →* H)
  (M : Rep ℤ Dw) (Q : Rep ℤ D) (C : Rep ℤ H)
  (iW : Rep.res (πH.comp i) M ⟶ Q) (φ : Q ⟶ Rep.res i C)

theorem summand_mul (h : H) (d : D) (x : M) :
    C.ρ (h * i d) (φ.hom (iW.hom ((Rep.res πH M).ρ (h * i d)⁻¹ x))) = C.ρ h (φ.hom (iW.hom ((Rep.res πH M).ρ h⁻¹ x))) := by
  have hφ : ∀ q : Q, C.ρ (i d) (φ.hom q) = φ.hom (Q.ρ d q) := fun q => (Rep.hom_comm_apply φ d q).symm
  have hiW : ∀ m : M, iW.hom (M.ρ (πH (i d)) m) = Q.ρ d (iW.hom m) := fun m => Rep.hom_comm_apply iW d m
  show C.ρ (h * i d) (φ.hom (iW.hom (M.ρ (πH (h * i d)⁻¹) x))) = C.ρ h (φ.hom (iW.hom (M.ρ (πH h⁻¹) x)))
  rw [map_mul C.ρ, Module.End.mul_apply, mul_inv_rev, map_mul πH, map_mul M.ρ, Module.End.mul_apply, hφ, ← hiW,
    ← Module.End.mul_apply (f := M.ρ (πH (i d))), ← map_mul M.ρ, ← map_mul πH, mul_inv_cancel, map_one, map_one,
    Module.End.one_apply]

end summand
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

end M4aHerbrand.S2Arith
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_infPart_apply coe_finPart_apply principalIdeles IdeleClassGroup IdeleGaloisDescent Bridge.genuineβ Bridge.genuineβ_fst Bridge.genuineβ_snd Bridge.finiteConorm_apply GenuineDescent.genuineDescentDatum subsingleton_ideleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum_act_fst_apply"
namespace S2Arith
p2m_open "M4aHerbrand"

theorem S2L2_genuineβ_concentrated
    (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    infPart ((Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι w x) : (AdeleRing (𝓞 F') F')ˣ)) = 1 ∧
    (∀ W'' : HeightOneSpectrum (𝓞 F'), W''.under (𝓞 F) ≠ w →
        finPart W'' ((Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι w x) : (AdeleRing (𝓞 F') F')ˣ)) = 1) ∧
    (∀ (W'' : HeightOneSpectrum (𝓞 F')) (hv : W''.under (𝓞 F) = w),
        ((finPart W'' ((Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι w x) : (AdeleRing (𝓞 F') F')ˣ)) : (W''.adicCompletion F')ˣ) : W''.adicCompletion F') =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W'', hv⟩ : w.Extension (𝓞 F')) (x : w.adicCompletion F)) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    apply Units.ext
    rw [coe_infPart_apply, Units.coe_map, MonoidHom.coe_coe, M4aHerbrand.Bridge.genuineβ_fst]
    have h1 : ((ι w x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
      rw [← coe_infPart_apply, (hι w x).2.2]
      rfl
    rw [h1, map_one]
    rfl
  ·
    intro W'' hW
    apply Units.ext
    rw [coe_finPart_apply, Units.coe_map, MonoidHom.coe_coe, M4aHerbrand.Bridge.genuineβ_snd,
      M4aHerbrand.Bridge.finiteConorm_apply]
    have h2 : ((ι w x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 (W''.under (𝓞 F)) = 1 := by
      rw [← coe_finPart_apply, (hι w x).2.1 _ hW]
      rfl
    rw [h2, map_one]
    rfl
  ·
    intro W'' hv
    rw [coe_finPart_apply, Units.coe_map, MonoidHom.coe_coe, M4aHerbrand.Bridge.genuineβ_snd,
      M4aHerbrand.Bridge.finiteConorm_apply]
    subst hv
    rw [← coe_finPart_apply, (hι _ x).1]

end M4aHerbrand.S2Arith
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"
p2m_reactivate "P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.groupCohomology.S2Alg"

theorem S2arith_hN
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']
    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (W : HeightOneSpectrum (𝓞 F'))
    (hle : (NumberField.PlaceDecomp.decomp E F' W) ≤ ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))
    (iW : Rep.res (((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))).comp (Subgroup.inclusion hle)) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ))
    (hiW : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iW.hom (Additive.ofMul x)) : (W.adicCompletion F')ˣ) : W.adicCompletion F') =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (x : (W.under (𝓞 F)).adicCompletion F))
    (κ : Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶ Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hκ : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ, κ.hom (Additive.ofMul x) =
      Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι (W.under (𝓞 F)) x)) : IdeleClassGroup (𝓞 F') F'))
    (φW : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ) ⟶ Rep.res (Subgroup.inclusion hle) (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))))
    (hφW : ∀ x : (W.adicCompletion F')ˣ, φW.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' W x) : IdeleClassGroup (𝓞 F') F'))
    [Fintype (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)] :
    ∀ x : Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ),
      κ.hom x = ∑ g : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range,
        (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))).ρ g.out (φW.hom (iW.hom ((Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)).ρ g.out⁻¹ x))) := by
  classical
  haveI instGalFF' : IsGalois F F' := IsGalois.tower_top_of_isGalois E F F'
  intro x

  have memHS : ∀ m : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars E m) ∈ ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) := fun m =>
    Subgroup.mem_comap.2 (by rw [M4aHerbrand.S2Arith.restrictNormalHom_restrictScalars]; exact one_mem _)

  have hS_mem : ∀ {a : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))}, a ∈ (Subgroup.inclusion hle).range → (a : (F' ≃ₐ[E] F')) ∈ (NumberField.PlaceDecomp.decomp E F' W) := by
    rintro a ⟨d, rfl⟩; exact d.2
  have hS_mem' : ∀ {a : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))}, (a : (F' ≃ₐ[E] F')) ∈ (NumberField.PlaceDecomp.decomp E F' W) → a ∈ (Subgroup.inclusion hle).range :=
    fun {a} ha => ⟨⟨a, ha⟩, Subtype.ext rfl⟩

  have hrep : ∀ h : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))), ∃ (m : F' ≃ₐ[F] F') (d : ↥(NumberField.PlaceDecomp.decomp E F' W)),
      h = (⟨AlgEquiv.restrictScalars E m, memHS m⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) * Subgroup.inclusion hle d := by
    intro h
    obtain ⟨m, d, hd, hmd⟩ := M4aHerbrand.S2Arith.exists_eq_restrictScalars_mul (E := E) W (h : (F' ≃ₐ[E] F')) (Subgroup.mem_comap.1 h.2)
    exact ⟨m, ⟨d, hd⟩, Subtype.ext hmd⟩
  choose mOf dOf hmd using hrep
  have hmk : ∀ h : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))), (QuotientGroup.mk (⟨AlgEquiv.restrictScalars E (mOf h), memHS (mOf h)⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)) = QuotientGroup.mk h := fun h =>
    QuotientGroup.eq.2 ⟨dOf h, (inv_mul_eq_of_eq_mul (hmd h)).symm⟩
  have hinj : ∀ a b : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))), (AlgEquiv.restrictScalars E (mOf a)) • W = (AlgEquiv.restrictScalars E (mOf b)) • W →
      (QuotientGroup.mk a : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)) = QuotientGroup.mk b := by
    intro a b hab
    rw [← hmk a, ← hmk b, QuotientGroup.eq]
    apply hS_mem'
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp, MulAction.mem_stabilizer_iff]
    change ((AlgEquiv.restrictScalars E (mOf a))⁻¹ * AlgEquiv.restrictScalars E (mOf b)) • W = W
    rw [mul_smul, ← hab, inv_smul_smul]

  have hΦ : ∀ g : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range),
      (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))).ρ g.out (φW.hom (iW.hom ((Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)).ρ g.out⁻¹ x))) =
      (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))).ρ (⟨AlgEquiv.restrictScalars E (mOf g.out), memHS (mOf g.out)⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) (φW.hom (iW.hom ((Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)).ρ (⟨AlgEquiv.restrictScalars E (mOf g.out), memHS (mOf g.out)⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))⁻¹ x))) := by
    intro g
    conv_lhs => rw [hmd g.out]
    exact M4aHerbrand.S2Arith.summand_mul ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Subgroup.inclusion hle) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ) (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) iW φW _ _ x

  have hΦn : ∀ (m : F' ≃ₐ[F] F') (hn : (AlgEquiv.restrictScalars E m) ∈ ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))),
      (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))).ρ (⟨(AlgEquiv.restrictScalars E m), hn⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))
        (φW.hom (iW.hom ((Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)).ρ (⟨(AlgEquiv.restrictScalars E m), hn⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))⁻¹ x))) =
      Additive.ofMul (QuotientGroup.mk (ι' ((AlgEquiv.restrictScalars E m) • W)
        (NumberField.PlaceTransport.transportUnits (AlgEquiv.restrictScalars E m) rfl (Additive.toMul (iW.hom x)))) : IdeleClassGroup (𝓞 F') F') := by
    intro m hn
    have h1 : ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (⟨(AlgEquiv.restrictScalars E m), hn⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))⁻¹ = 1 := by
      apply Subtype.ext
      rw [map_inv]
      change ((AlgEquiv.restrictNormalHom F (AlgEquiv.restrictScalars E m))⁻¹ : F ≃ₐ[E] F) = 1
      rw [M4aHerbrand.S2Arith.restrictNormalHom_restrictScalars, inv_one]
    change ((Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))).ρ (AlgEquiv.restrictScalars E m) (φW.hom (iW.hom (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)).ρ (((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (⟨(AlgEquiv.restrictScalars E m), hn⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))⁻¹) x))) = _
    rw [h1, map_one, Module.End.one_apply, show iW.hom x = Additive.ofMul (Additive.toMul (iW.hom x)) from rfl, hφW,
      Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, hact']
    change Additive.ofMul (QuotientGroup.mk (D'.unitsAct (AlgEquiv.restrictScalars E m) (ι' W (Additive.toMul (iW.hom x)))) : IdeleClassGroup (𝓞 F') F') = _
    rw [M4aHerbrand.S2Arith.S2L1_unitsAct_concentrated E F' D' ι' hι']
    rfl

  have hL2 := M4aHerbrand.S2Arith.S2L2_genuineβ_concentrated F F' ι hι (W.under (𝓞 F)) (Additive.toMul x)
  have key : (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι (W.under (𝓞 F)) (Additive.toMul x)) : (AdeleRing (𝓞 F') F')ˣ) =
      ∏ g : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range), ι' ((AlgEquiv.restrictScalars E (mOf g.out)) • W)
        (NumberField.PlaceTransport.transportUnits (AlgEquiv.restrictScalars E (mOf g.out)) rfl (Additive.toMul (iW.hom x))) := by
    apply M4aHerbrand.S2Arith.idele_ext
    · rw [hL2.1, map_prod, Finset.prod_eq_one (fun g _ => (hι' _ _).2.2)]
    · intro W''
      rw [map_prod]
      by_cases hv : W''.under (𝓞 F) = W.under (𝓞 F)
      ·
        have horb : W'' ∈ MulAction.orbit (F' ≃ₐ[F] F') W := by
          rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq F F' W]; exact hv
        obtain ⟨m₀, hm₀⟩ := horb
        have e : (AlgEquiv.restrictScalars E (mOf (QuotientGroup.mk (⟨AlgEquiv.restrictScalars E m₀, memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)).out)) • W = W'' := by
          have h1 : (((⟨(AlgEquiv.restrictScalars E m₀), memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))))⁻¹ *
              (QuotientGroup.mk (⟨(AlgEquiv.restrictScalars E m₀), memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)).out : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (F' ≃ₐ[E] F')) ∈ (NumberField.PlaceDecomp.decomp E F' W) :=
            hS_mem (QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm)
          have h2 := eq_mul_inv_of_mul_eq (congrArg Subtype.val (hmd (QuotientGroup.mk (⟨(AlgEquiv.restrictScalars E m₀), memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)).out)).symm
          change (AlgEquiv.restrictScalars E (mOf (QuotientGroup.mk (⟨AlgEquiv.restrictScalars E m₀, memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)).out)) = _ at h2
          rw [h2, ← mul_inv_cancel_left ((AlgEquiv.restrictScalars E m₀))
            ((QuotientGroup.mk (⟨(AlgEquiv.restrictScalars E m₀), memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)).out : (F' ≃ₐ[E] F')), mul_assoc, mul_smul]
          have h3 : (((AlgEquiv.restrictScalars E m₀))⁻¹ * ((QuotientGroup.mk (⟨(AlgEquiv.restrictScalars E m₀), memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)).out : (F' ≃ₐ[E] F')) *
              ((Subgroup.inclusion hle (dOf (QuotientGroup.mk (⟨(AlgEquiv.restrictScalars E m₀), memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range)).out) : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (F' ≃ₐ[E] F'))⁻¹) • W = W := by
            rw [← MulAction.mem_stabilizer_iff, NumberField.PlaceTransport.stabilizer_eq_decomp]
            exact mul_mem h1 (inv_mem (dOf _).2)
          rw [h3]
          exact hm₀
        subst e
        rw [Finset.prod_eq_single (QuotientGroup.mk (⟨(AlgEquiv.restrictScalars E m₀), memHS m₀⟩ : ↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))) : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range))]
        · rw [(hι' _ _).1]
          apply Units.ext
          rw [hL2.2.2 _ hv]
          change _ = NumberField.PlaceTransport.transport _ rfl ((Additive.toMul (iW.hom x) : (W.adicCompletion F')ˣ) : W.adicCompletion F')
          rw [show iW.hom x = iW.hom (Additive.ofMul (Additive.toMul x)) from rfl, hiW]
          exact (NumberField.PlaceTransport.transport_adicCompletionSemialgHom F F' _
            (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) ⟨_, hv⟩ rfl _).symm
        · intro g _ hne
          apply (hι' _ _).2.1
          intro heq
          exact hne ((QuotientGroup.out_eq' g).symm.trans ((hinj _ _ heq.symm).trans (QuotientGroup.out_eq' _)))
        · intro h; exact absurd (Finset.mem_univ _) h
      ·
        rw [hL2.2.1 W'' hv, Finset.prod_eq_one]
        intro g _
        apply (hι' _ _).2.1
        intro heq
        apply hv
        rw [heq, M4aHerbrand.S2Arith.under_smul, M4aHerbrand.S2Arith.restrictNormalHom_restrictScalars, one_smul]

  calc κ.hom x = _ := hκ (Additive.toMul x)
    _ = Additive.ofMul ((QuotientGroup.mk' (principalIdeles (𝓞 F') F')) (∏ g : (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range), ι' ((AlgEquiv.restrictScalars E (mOf g.out)) • W)
          (NumberField.PlaceTransport.transportUnits (AlgEquiv.restrictScalars E (mOf g.out)) rfl (Additive.toMul (iW.hom x))))) :=
        congrArg (fun u : (AdeleRing (𝓞 F') F')ˣ => Additive.ofMul ((QuotientGroup.mk' (principalIdeles (𝓞 F') F')) u)) key
    _ = _ := by
        rw [map_prod, ofMul_prod]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [hΦ g, hΦn (mOf g.out) (memHS (mOf g.out))]
        rfl

theorem solution
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)

    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)

    (W : HeightOneSpectrum (𝓞 F'))
    (r : ↥(NumberField.PlaceDecomp.decomp E F' W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : F),
      algebraMap F F' (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : F' ≃ₐ[E] F') (algebraMap F F' x))
    (hle : NumberField.PlaceDecomp.decomp E F' W ≤
      (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))

    (iW : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ)
    (hiW : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iW.hom (Additive.ofMul x)) : (W.adicCompletion F')ˣ) : W.adicCompletion F') =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (x : (W.under (𝓞 F)).adicCompletion F))

    (κ : Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
          (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hκ : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ, κ.hom (Additive.ofMul x) =
      Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι (W.under (𝓞 F)) x)) : IdeleClassGroup (𝓞 F') F'))

    (φW : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ ⟶
        Rep.res (Subgroup.inclusion hle)
          (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
            (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))))
    (hφW : ∀ x : (W.adicCompletion F')ˣ, φW.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' W x) : IdeleClassGroup (𝓞 F') F'))
    (k : ℤ)
    (z : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) 2)
    (y : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
          (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2)
    (hy : k • (groupCohomology.map (Subgroup.inclusion hle)
            (𝟙 (Rep.res (Subgroup.inclusion hle)
              (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
                (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))))) 2).hom y =
          k • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' W)) φW 2).hom ((groupCohomology.map r iW 2).hom z)) :
    k • (groupCohomology.map ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) κ 2).hom z =
      k • ((((NumberField.PlaceDecomp.decomp E F' W).subgroupOf
              ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))).index : ℤ) • y) := by

  have hr' : r = (((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))).comp (Subgroup.inclusion hle) := by
    refine MonoidHom.ext fun σ => Subtype.ext (AlgEquiv.ext fun x => ?_)
    apply (algebraMap F F').injective
    rw [hr σ x]
    exact (AlgEquiv.restrictNormal_commutes (σ : F' ≃ₐ[E] F') F x).symm
  subst hr'
  letI : Fintype (↥((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))) ⧸ (Subgroup.inclusion hle).range) := Fintype.ofFinite _
  have key := groupCohomology.S2Alg.glue (k := ℤ) ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) _ iW φW κ
    (S2arith_hN E F F' D' hact' ι' hι' ι hι W hle iW hiW κ hκ φW hφW) 2 k z y hy
  rw [Subgroup.inclusion_range] at key
  rw [key, natCast_zsmul]

end S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp
end P2MW
export P2MW.S_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp (solution)
