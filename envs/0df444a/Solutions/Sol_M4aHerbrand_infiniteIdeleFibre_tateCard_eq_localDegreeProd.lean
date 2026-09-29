-- Prove2me | solution 1 for M4aHerbrand.infiniteIdeleFibre_tateCard_eq_localDegreeProd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/edb71a72-7e28-5f7a-a794-81cabd6a1d6c

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits
import Theorems.Thm_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv
import Theorems.Thm_NumberField_ArchIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1
import Theorems.Thm_NumberField_InfPlaceDecomp_card_over_mul_card_decomp_above
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd

set_option autoImplicit false
open NumberField IsDedekindDomain

namespace P2mS26GA

attribute [local instance 2000] Rep.hV2 Rep.hV1

open NumberField NumberField.InfinitePlaceTransport
open scoped NumberField.InfPlaceDecomp

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev AFib (v : InfinitePlace K) : Type := {w : InfinitePlace L // w.comap (algebraMap K L) = v}

theorem act_coord (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L)
    {w w' : InfinitePlace L} (h : σ • w = w') : (D.act σ x).1 w' = transport σ h (x.1 w) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  rw [Subsingleton.elim D (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x h

variable {K L}

theorem comap_smul_algebraMap (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) :=
  InfinitePlace.ext _ _ fun x => by
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply, InfinitePlace.smul_apply, AlgEquiv.commutes]

theorem inv_smul_mem (σ : L ≃ₐ[K] L) {v : InfinitePlace K} (w : AFib K L v) : (σ⁻¹ • w.1).comap (algebraMap K L) = v :=
  (comap_smul_algebraMap σ⁻¹ w.1).trans w.2

noncomputable def sh (σ : L ≃ₐ[K] L) {v : InfinitePlace K} (w : AFib K L v) : AFib K L v := ⟨σ⁻¹ • w.1, inv_smul_mem σ w⟩

theorem smul_sh (σ : L ≃ₐ[K] L) {v : InfinitePlace K} (w : AFib K L v) : σ • (sh σ w).1 = w.1 := smul_inv_smul σ w.1

section ext
variable {v : InfinitePlace K}

open Classical in

noncomputable def ext1 (u : Π w : AFib K L v, w.1.Completion) : InfiniteAdeleRing L :=
  fun w => if h : w.comap (algebraMap K L) = v then u ⟨w, h⟩ else 1

open Classical in
theorem ext1_apply (u : Π w : AFib K L v, w.1.Completion) (w : AFib K L v) : ext1 u w.1 = u w := by
  obtain ⟨w, rfl⟩ := w
  show (if h : w.comap (algebraMap K L) = w.comap (algebraMap K L) then u ⟨w, h⟩ else 1) = u ⟨w, rfl⟩
  rw [dif_pos rfl]

end ext

section pinned
variable (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem phiA_apply
    (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (hΦa : ∀ (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (x : InfiniteAdeleRing L),
      (∀ w : AFib K L v, x w.1 = (u : Π w : AFib K L v, w.1.Completion) w) →
      ∀ w : AFib K L v, (D.act σ (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 w.1 = (Φa v u : Π w : AFib K L v, w.1.Completion) w)
    (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (w : AFib K L v) :
    (Φa v u : Π w : AFib K L v, w.1.Completion) w
      = transport σ (smul_sh σ w) ((u : Π w : AFib K L v, w.1.Completion) (sh σ w)) := by
  rw [← hΦa v u (ext1 (u : Π w : AFib K L v, w.1.Completion)) (ext1_apply _) w, act_coord K L D σ _ (smul_sh σ w)]
  show transport σ (smul_sh σ w) (ext1 (u : Π w : AFib K L v, w.1.Completion) (sh σ w).1) = _
  rw [ext1_apply]

end pinned

section ident
variable [IsGalois K L]

noncomputable def heartA (v : InfinitePlace K) :
    (Rep.coind (InfPlaceDecomp.decomp K L (ArchIdele.above K L v)).subtype (InfPlaceDecomp.localUnits K L (ArchIdele.above K L v)))
      ≃+ Additive (Π w : AFib K L v, (w.1.Completion)ˣ) :=
  (NumberField.ArchIdele.exists_addEquiv_coind_localUnits K L v).choose

theorem heartA_spec (v : InfinitePlace K) (g : L ≃ₐ[K] L) (f) (w w' : AFib K L v) (h : g • w'.1 = w.1) :
    Additive.toMul (heartA v ((Rep.coind (InfPlaceDecomp.decomp K L (ArchIdele.above K L v)).subtype
      (InfPlaceDecomp.localUnits K L (ArchIdele.above K L v))).ρ g f)) w
      = transportUnits g h (Additive.toMul (heartA v f) w') :=
  (NumberField.ArchIdele.exists_addEquiv_coind_localUnits K L v).choose_spec g f w w' h

abbrev XA : Type := Π v : InfinitePlace K, (Π w : AFib K L v, w.1.Completion)ˣ

noncomputable def toF (u : XA (K := K) (L := L)) : (v : InfinitePlace K) → ArchIdele.fibre K L v :=
  fun v => (heartA v).symm (Additive.ofMul (MulEquiv.piUnits (u v)))

noncomputable def ofF (f : (v : InfinitePlace K) → ArchIdele.fibre K L v) : XA (K := K) (L := L) :=
  fun v => MulEquiv.piUnits.symm (Additive.toMul (heartA v (f v)))

theorem toF_apply (u : XA (K := K) (L := L)) (v : InfinitePlace K) :
    toF u v = (heartA v).symm (Additive.ofMul (MulEquiv.piUnits (u v))) := rfl

theorem ofF_toF (u : XA (K := K) (L := L)) : ofF (toF u) = u := funext fun v => by
  show MulEquiv.piUnits.symm (Additive.toMul (heartA v ((heartA v).symm (Additive.ofMul (MulEquiv.piUnits (u v)))))) = u v
  rw [AddEquiv.apply_symm_apply, toMul_ofMul, MulEquiv.symm_apply_apply]

theorem toF_ofF (f : (v : InfinitePlace K) → ArchIdele.fibre K L v) : toF (ofF f) = f := funext fun v => by
  show (heartA v).symm (Additive.ofMul (MulEquiv.piUnits (MulEquiv.piUnits.symm (Additive.toMul (heartA v (f v)))))) = f v
  rw [MulEquiv.apply_symm_apply, ofMul_toMul, AddEquiv.symm_apply_apply]

set_option maxHeartbeats 3200000 in
theorem toF_mul (u u' : XA (K := K) (L := L)) : toF (u * u') = toF u + toF u' := funext fun v => by
  show (heartA v).symm (Additive.ofMul (MulEquiv.piUnits ((u * u') v))) = (heartA v).symm _ + (heartA v).symm _
  rw [Pi.mul_apply, map_mul, ofMul_mul, map_add]

set_option maxHeartbeats 3200000 in

noncomputable def ident : Additive (XA (K := K) (L := L)) ≃+ (ArchIdele.obj K L) where
  toFun x := toF (Additive.toMul x)
  invFun f := Additive.ofMul (ofF f)
  left_inv x := by
    show Additive.ofMul (ofF (toF (Additive.toMul x))) = x
    rw [ofF_toF, ofMul_toMul]
  right_inv f := by
    show toF (ofF (Additive.toMul (Additive.ofMul f))) = f
    rw [toMul_ofMul, toF_ofF]
  map_add' x y := by
    show toF (Additive.toMul (x + y)) = toF (Additive.toMul x) + toF (Additive.toMul y)
    rw [toMul_add, toF_mul]

theorem ident_apply (x : Additive (XA (K := K) (L := L))) : ident x = toF (Additive.toMul x) := rfl

noncomputable def phiX (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (u : XA (K := K) (L := L)) : XA (K := K) (L := L) :=
  fun v => Φa v (u v)

set_option maxHeartbeats 3200000 in

theorem ident_phiX (σ : L ≃ₐ[K] L)
    (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (hA : ∀ (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (w : AFib K L v),
      ((Φa v u : (Π w : AFib K L v, w.1.Completion)ˣ) : Π w : AFib K L v, w.1.Completion) w
      = transport σ (smul_sh σ w) ((u : Π w : AFib K L v, w.1.Completion) (sh σ w)))
    (u : XA (K := K) (L := L)) :
    ident (Additive.ofMul (phiX Φa u)) = (ArchIdele.obj K L).ρ σ (ident (Additive.ofMul u)) := by
  rw [ident_apply, ident_apply, toMul_ofMul, toMul_ofMul]
  funext v
  rw [GroupCohomology.RepPi.obj_rho_apply]
  show (heartA v).symm (Additive.ofMul (MulEquiv.piUnits (phiX Φa u v)))
    = (Rep.coind (InfPlaceDecomp.decomp K L (ArchIdele.above K L v)).subtype
        (InfPlaceDecomp.localUnits K L (ArchIdele.above K L v))).ρ σ
        ((heartA v).symm (Additive.ofMul (MulEquiv.piUnits (u v))))
  apply (heartA v).injective
  rw [AddEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  funext w
  rw [toMul_ofMul, heartA_spec v σ _ w (sh σ w) (smul_sh σ w), AddEquiv.apply_symm_apply, toMul_ofMul]
  refine Units.ext ?_
  exact hA v (u v) w

set_option maxHeartbeats 3200000 in

theorem ident_phiX_pow (σ : L ≃ₐ[K] L)
    (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (hA : ∀ (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (w : AFib K L v),
      ((Φa v u : (Π w : AFib K L v, w.1.Completion)ˣ) : Π w : AFib K L v, w.1.Completion) w
      = transport σ (smul_sh σ w) ((u : Π w : AFib K L v, w.1.Completion) (sh σ w)))
    (i : ℕ) (u : XA (K := K) (L := L)) :
    ident (Additive.ofMul ((fun v => (Φa v ^ i) (u v)) : XA (K := K) (L := L)))
      = (ArchIdele.obj K L).ρ (σ ^ i) (ident (Additive.ofMul u)) := by
  induction i with
  | zero =>
    simp only [pow_zero, MulAut.one_apply, map_one, Module.End.one_apply]
  | succ i ih =>
    have : ((fun v => (Φa v ^ (i + 1)) (u v)) : XA (K := K) (L := L)) = phiX Φa (fun v => (Φa v ^ i) (u v)) := by
      funext v
      show (Φa v ^ (i + 1)) (u v) = Φa v ((Φa v ^ i) (u v)); rw [pow_succ']; rfl
    rw [this, ident_phiX σ Φa hA, ih, pow_succ', map_mul]
    rfl

set_option maxHeartbeats 3200000 in

theorem hd_ident (σ : L ≃ₐ[K] L)
    (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (hA : ∀ (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (w : AFib K L v),
      ((Φa v u : (Π w : AFib K L v, w.1.Completion)ˣ) : Π w : AFib K L v, w.1.Completion) w
      = transport σ (smul_sh σ w) ((u : Π w : AFib K L v, w.1.Completion) (sh σ w)))
    (d : Additive (XA (K := K) (L := L)) →+ Additive (XA (K := K) (L := L)))
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul ((fun v => Φa v (u v))) - Additive.ofMul u)
    (x : Additive (XA (K := K) (L := L))) :
    ident (d x) = (ArchIdele.obj K L).ρ σ (ident x) - ident x := by
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = x := ⟨Additive.toMul x, rfl⟩
  rw [hd u]
  exact (map_sub ident _ _).trans (congrArg (· - ident (Additive.ofMul u)) (ident_phiX σ Φa hA u))

set_option maxHeartbeats 3200000 in

theorem hN_ident (σ : L ≃ₐ[K] L)
    (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (hA : ∀ (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (w : AFib K L v),
      ((Φa v u : (Π w : AFib K L v, w.1.Completion)ˣ) : Π w : AFib K L v, w.1.Completion) w
      = transport σ (smul_sh σ w) ((u : Π w : AFib K L v, w.1.Completion) (sh σ w)))
    (n : ℕ) (N : Additive (XA (K := K) (L := L)) →+ Additive (XA (K := K) (L := L)))
    (hN : ∀ u, N (Additive.ofMul u) = ∑ i ∈ Finset.range n, Additive.ofMul ((fun v => (Φa v ^ i) (u v))))
    (x : Additive (XA (K := K) (L := L))) :
    ident (N x) = ∑ i ∈ Finset.range n, (ArchIdele.obj K L).ρ (σ ^ i) (ident x) := by
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = x := ⟨Additive.toMul x, rfl⟩
  rw [hN u]
  exact (map_sum ident _ _).trans (Finset.sum_congr rfl fun i _ => ident_phiX_pow σ Φa hA i u)

end ident

end P2mS26GA

set_option maxHeartbeats 3200000 in

theorem P2mS26GA.infiniteIdeleFibre_u0
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (Φa : (v : InfinitePlace K) →
      (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ ≃*
      (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ)
    (hΦa : ∀ (v : InfinitePlace K)
      (u : (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ)
      (x : InfiniteAdeleRing L),
      (∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        x w.1 = (u : Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion) w) →
      ∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        (D.act σ (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 w.1 =
          (Φa v u : Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
            w.1.Completion) w)

    (d : Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ) →+
      Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φa v (u v))) - Additive.ofMul u)
    (N : Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ) →+
      Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φa v ^ i) (u v))))

    (si : InfinitePlace K → ℕ)
    (hsi : ∀ v, si v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / si v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsCyclic (L ≃ₐ[K] L) := by
    first
    | exact ⟨⟨σ, hσ⟩⟩
    | exact ⟨⟨σ, fun τ => (Subgroup.mem_zpowers_iff.1 (hσ τ))⟩⟩

  have hA := P2mS26GA.phiA_apply σ D Φa hΦa

  have hd' := P2mS26GA.hd_ident σ Φa hA d hd
  have hN' := P2mS26GA.hN_ident σ Φa hA (Nat.card (L ≃ₐ[K] L)) N hN
  obtain ⟨h0, h1⟩ := Rep.natCard_kerModRange_eq_natCard_tate_of_addEquiv (NumberField.ArchIdele.obj K L) σ hσ
    P2mS26GA.ident d hd' N hN'

  have hBJ := NumberField.ArchIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1 K L
  refine ⟨?_, ?_⟩
  · rw [h0, hBJ.1]
    refine Finset.prod_congr rfl fun v _ => ?_
    have h25 := NumberField.InfPlaceDecomp.card_over_mul_card_decomp_above K L v
    have hpos : 0 < Nat.card {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
      Nat.pos_of_ne_zero fun h0 => (Nat.card_pos (α := L ≃ₐ[K] L)).ne' (by rw [← h25, h0, zero_mul])
    rw [hsi v, ← h25, Nat.mul_div_cancel_left _ hpos]
  · rw [h1]
    exact Nat.card_eq_one_iff_unique.2 ⟨hBJ.2, ⟨0⟩⟩

namespace P2mS26UnivA
noncomputable section

open IsDedekindDomain NumberField

universe uK uL

section generic
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerEquiv (Θ : A ≃+ B) (d : A →+ A) (d' : B →+ B) (hd : ∀ a, Θ (d a) = d' (Θ a)) : d.ker ≃+ d'.ker where
  toFun a := ⟨Θ (a : A), by rw [AddMonoidHom.mem_ker, ← hd, (AddMonoidHom.mem_ker).1 a.2, map_zero]⟩
  invFun b := ⟨Θ.symm (b : B), by
    rw [AddMonoidHom.mem_ker, ← Θ.injective.eq_iff, hd, AddEquiv.apply_symm_apply, map_zero]
    exact b.2⟩
  left_inv a := Subtype.ext (Θ.symm_apply_apply (a : A))
  right_inv b := Subtype.ext (Θ.apply_symm_apply (b : B))
  map_add' a b := Subtype.ext (map_add Θ (a : A) (b : A))

theorem card_kerModRange_eq_of_addEquiv (Θ : A ≃+ B) (d N : A →+ A) (d' N' : B →+ B)
    (hd : ∀ a, Θ (d a) = d' (Θ a)) (hN : ∀ a, Θ (N a) = N' (Θ a)) :
    Nat.card (d.ker ⧸ N.range.addSubgroupOf d.ker) = Nat.card (d'.ker ⧸ N'.range.addSubgroupOf d'.ker) := by
  refine Nat.card_congr (QuotientAddGroup.congr (N.range.addSubgroupOf d.ker) (N'.range.addSubgroupOf d'.ker)
    (kerEquiv Θ d d' hd) ?_).toEquiv
  ext ⟨b, hb⟩
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨x, hx⟩, hab⟩
    refine ⟨Θ x, ?_⟩
    have : Θ a = b := congrArg Subtype.val hab
    rw [← hN, hx]
    exact this
  · rintro ⟨y, hy⟩
    refine ⟨⟨Θ.symm b, ?_⟩, ⟨Θ.symm y, ?_⟩, Subtype.ext (Θ.apply_symm_apply b)⟩
    · rw [AddMonoidHom.mem_ker, ← Θ.injective.eq_iff, hd, AddEquiv.apply_symm_apply, map_zero]; exact hb
    · rw [← Θ.injective.eq_iff, hN, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hy]

theorem exists_conj (Θ : A ≃+ B) (d : A →+ A) : ∃ d' : B →+ B, ∀ a, Θ (d a) = d' (Θ a) :=
  ⟨Θ.toAddMonoidHom.comp (d.comp Θ.symm.toAddMonoidHom), fun a => by
    show Θ (d a) = Θ (d (Θ.symm (Θ a)))
    rw [AddEquiv.symm_apply_apply]⟩

end generic

theorem small (L : Type uL) [Field L] [NumberField L] : Small.{0} L :=
  haveI : Countable L := Countable.of_equiv _ (Module.finBasis ℚ L).equivFun.toEquiv.symm
  inferInstance

attribute [local instance] small

section models
variable (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def eqv : L ≃+* Shrink.{0} L := (Shrink.ringEquiv L).symm

theorem numberField : NumberField (Shrink.{0} L) := NumberField.of_ringEquiv L _ (eqv L)
attribute [local instance] numberField

@[reducible] def alg : Algebra (Shrink.{0} K) (Shrink.{0} L) :=
  ((eqv L : L →+* Shrink.{0} L).comp ((algebraMap K L).comp ((eqv K).symm : Shrink.{0} K →+* K))).toAlgebra
attribute [local instance] alg

theorem algebraMap_eqv (k : K) : algebraMap (Shrink.{0} K) (Shrink.{0} L) (eqv K k) = eqv L (algebraMap K L k) := by
  show eqv L (algebraMap K L ((eqv K).symm (eqv K k))) = _
  rw [RingEquiv.symm_apply_apply]

theorem algebraMap_comp_eqv : (algebraMap (Shrink.{0} K) (Shrink.{0} L)).comp (eqv K : K →+* Shrink.{0} K)
    = (eqv L : L →+* Shrink.{0} L).comp (algebraMap K L) :=
  RingHom.ext (algebraMap_eqv K L)

theorem isGalois [IsGalois K L] : IsGalois (Shrink.{0} K) (Shrink.{0} L) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  exact IsGalois.of_equiv_equiv (F := K) (E := L) (f := eqv K) (g := eqv L) (algebraMap_comp_eqv K L)

def gal (σ : L ≃ₐ[K] L) : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L :=
  AlgEquiv.ofRingEquiv (f := ((eqv L).symm.trans (σ : L ≃+* L)).trans (eqv L)) (fun x => by
    obtain ⟨k, rfl⟩ := (eqv K).surjective x
    show eqv L (σ ((eqv L).symm (algebraMap _ _ (eqv K k)))) = _
    rw [algebraMap_eqv, RingEquiv.symm_apply_apply, AlgEquiv.commutes])

theorem gal_apply (σ : L ≃ₐ[K] L) (x : L) : gal K L σ (eqv L x) = eqv L (σ x) := by
  show eqv L (σ ((eqv L).symm (eqv L x))) = _
  rw [RingEquiv.symm_apply_apply]

theorem eqv_symm_gal (σ : L ≃ₐ[K] L) (y : Shrink.{0} L) : (eqv L).symm (gal K L σ y) = σ ((eqv L).symm y) := by
  obtain ⟨x, rfl⟩ := (eqv L).surjective y
  rw [gal_apply, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

def galInv (τ : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) : L ≃ₐ[K] L :=
  AlgEquiv.ofRingEquiv (f := ((eqv L).trans (τ : Shrink.{0} L ≃+* Shrink.{0} L)).trans (eqv L).symm) (fun k => by
    show (eqv L).symm (τ (eqv L (algebraMap K L k))) = _
    rw [← algebraMap_eqv, AlgEquiv.commutes, algebraMap_eqv, RingEquiv.symm_apply_apply])

def galEquiv : (L ≃ₐ[K] L) ≃* (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) where
  toFun := gal K L
  invFun := galInv K L
  left_inv σ := AlgEquiv.ext fun x => by
    show (eqv L).symm (gal K L σ (eqv L x)) = σ x
    rw [gal_apply, RingEquiv.symm_apply_apply]
  right_inv τ := AlgEquiv.ext fun y => by
    obtain ⟨x, rfl⟩ := (eqv L).surjective y
    rw [gal_apply]
    show eqv L ((eqv L).symm (τ (eqv L x))) = _
    rw [RingEquiv.apply_symm_apply]
  map_mul' σ τ := AlgEquiv.ext fun y => by
    obtain ⟨x, rfl⟩ := (eqv L).surjective y
    rw [gal_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, gal_apply, gal_apply]

theorem galEquiv_apply (σ : L ≃ₐ[K] L) : galEquiv K L σ = gal K L σ := rfl

theorem card_gal : Nat.card (L ≃ₐ[K] L) = Nat.card (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) :=
  Nat.card_congr (galEquiv K L).toEquiv

theorem gal_generates {σ : L ≃ₐ[K] L} (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (τ : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) : τ ∈ Subgroup.zpowers (gal K L σ) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ ((galEquiv K L).symm τ))
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← galEquiv_apply, ← map_zpow, hk, MulEquiv.apply_symm_apply]⟩

theorem gal_inv (σ : L ≃ₐ[K] L) : gal K L σ⁻¹ = (gal K L σ)⁻¹ := by
  rw [← galEquiv_apply, map_inv]; rfl

theorem gal_pow (σ : L ≃ₐ[K] L) (i : ℕ) : gal K L (σ ^ i) = (gal K L σ) ^ i := by
  rw [← galEquiv_apply, map_pow]; rfl

theorem gal_symm_apply (σ : L ≃ₐ[K] L) (x : L) : (gal K L σ).symm (eqv L x) = eqv L (σ.symm x) := by
  apply (gal K L σ).injective
  rw [AlgEquiv.apply_symm_apply, gal_apply, AlgEquiv.apply_symm_apply]

def iplc : InfinitePlace L ≃ InfinitePlace (Shrink.{0} L) where
  toFun w := w.comap ((eqv L).symm : Shrink.{0} L →+* L)
  invFun w0 := w0.comap (eqv L : L →+* Shrink.{0} L)
  left_inv w := InfinitePlace.ext _ _ fun x => by
    show w ((eqv L).symm (eqv L x)) = w x
    rw [RingEquiv.symm_apply_apply]
  right_inv w0 := InfinitePlace.ext _ _ fun y => by
    show w0 (eqv L ((eqv L).symm y)) = w0 y
    rw [RingEquiv.apply_symm_apply]

theorem iplc_apply (w : InfinitePlace L) (y : Shrink.{0} L) : iplc L w y = w ((eqv L).symm y) := rfl

theorem iplc_apply_eqv (w : InfinitePlace L) (x : L) : iplc L w (eqv L x) = w x := by
  rw [iplc_apply, RingEquiv.symm_apply_apply]

theorem comap_iplc (w : InfinitePlace L) :
    (iplc L w).comap (algebraMap (Shrink.{0} K) (Shrink.{0} L)) = iplc K (w.comap (algebraMap K L)) :=
  InfinitePlace.ext _ _ fun y => by
    obtain ⟨k, rfl⟩ := (eqv K).surjective y
    rw [InfinitePlace.comap_apply, algebraMap_eqv, iplc_apply_eqv, iplc_apply_eqv, InfinitePlace.comap_apply]

theorem iplc_smul (σ : L ≃ₐ[K] L) (w : InfinitePlace L) : iplc L (σ • w) = gal K L σ • iplc L w :=
  InfinitePlace.ext _ _ fun y => by
    obtain ⟨x, rfl⟩ := (eqv L).surjective y
    rw [iplc_apply_eqv, InfinitePlace.smul_apply, InfinitePlace.smul_apply, gal_symm_apply, iplc_apply_eqv]

end models

attribute [local instance] numberField alg isGalois

section completion
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField.InfinitePlaceTransport

variable {w : InfinitePlace L} {w0 : InfinitePlace (Shrink.{0} L)}

theorem apply_eqv_of_iplc (hw : iplc L w = w0) (x : L) : w0 (eqv L x) = w x := by
  rw [← hw, iplc_apply_eqv]

theorem apply_symm_of_iplc (hw : iplc L w = w0) (y : Shrink.{0} L) : w ((eqv L).symm y) = w0 y := by
  rw [← hw, iplc_apply]

theorem uniformContinuous_icongr (hw : iplc L w = w0) : UniformContinuous (WithAbs.congr w.1 w0.1 (eqv L)) :=
  uniformContinuous_congr_of_forall_eq w.1 w0.1 _ (apply_eqv_of_iplc hw)

theorem uniformContinuous_icongr_symm (hw : iplc L w = w0) : UniformContinuous (WithAbs.congr w0.1 w.1 (eqv L).symm) :=
  uniformContinuous_congr_of_forall_eq w0.1 w.1 _ (apply_symm_of_iplc hw)

def icpl (hw : iplc L w = w0) : w.Completion ≃+* w0.Completion :=
  (NumberField.InfinitePlace.Completion.equiv w).trans
    ((UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w0.1 (eqv L))
      (uniformContinuous_icongr hw).continuous
      (by rw [WithAbs.congr_symm]; exact (uniformContinuous_icongr_symm hw).continuous)).trans
    (NumberField.InfinitePlace.Completion.equiv w0).symm)

theorem icpl_apply (hw : iplc L w = w0) (x : w.Completion) :
    (icpl hw x).toCompletion = UniformSpace.Completion.map (WithAbs.congr w.1 w0.1 (eqv L)) x.toCompletion :=
  rfl

theorem icpl_coe (hw : iplc L w = w0) (x : WithAbs w.1) :
    icpl hw (x : w.Completion) = ((WithAbs.congr w.1 w0.1 (eqv L) x : WithAbs w0.1) : w0.Completion) := by
  apply NumberField.InfinitePlace.Completion.ext
  rw [icpl_apply, NumberField.InfinitePlace.Completion.coe_toCompletion,
    NumberField.InfinitePlace.Completion.coe_toCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_icongr hw)]

theorem continuous_icpl (hw : iplc L w = w0) : Continuous (icpl hw) := by
  rw [show (icpl hw : w.Completion → w0.Completion) =
      NumberField.InfinitePlace.Completion.ofCompletion ∘ UniformSpace.Completion.map _ ∘
        NumberField.InfinitePlace.Completion.toCompletion from
      funext fun x => NumberField.InfinitePlace.Completion.ext (h := icpl_apply hw x)]
  exact (NumberField.InfinitePlace.Completion.continuous_ofCompletion _).comp
    (UniformSpace.Completion.continuous_map.comp (NumberField.InfinitePlace.Completion.continuous_toCompletion _))

abbrev icplUnits (hw : iplc L w = w0) : (w.Completion)ˣ ≃* (w0.Completion)ˣ := Units.mapEquiv (icpl hw).toMulEquiv

theorem icpl_transport (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w')
    {w0 w0' : InfinitePlace (Shrink.{0} L)} (hw : iplc L w = w0) (hw' : iplc L w' = w0')
    (h0 : gal K L σ • w0 = w0') (x : w.Completion) :
    icpl hw' (transport σ h x) = transport (gal K L σ) h0 (icpl hw x) := by
  refine NumberField.InfinitePlace.Completion.induction_on (v := w)
    (p := fun x => icpl hw' (transport σ h x) = transport (gal K L σ) h0 (icpl hw x)) x
    (isClosed_eq ((continuous_icpl hw').comp (continuous_transport σ h))
      ((continuous_transport (gal K L σ) h0).comp (continuous_icpl hw))) fun a => ?_
  show icpl hw' (transport σ h (a : w.Completion)) = transport (gal K L σ) h0 (icpl hw (a : w.Completion))
  rw [transport_coe, icpl_coe, icpl_coe, transport_coe]
  congr 1
  simp only [WithAbs.congr_apply, AlgEquiv.coe_ringEquiv, gal_apply]

end completion

section coord
variable (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
open NumberField.InfinitePlaceTransport

abbrev AFib (v : InfinitePlace K) : Type uL := {w : InfinitePlace L // w.comap (algebraMap K L) = v}

abbrev AFib0 (v0 : InfinitePlace (Shrink.{0} K)) : Type :=
  {w0 : InfinitePlace (Shrink.{0} L) // w0.comap (algebraMap (Shrink.{0} K) (Shrink.{0} L)) = v0}

theorem act_coord (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L)
    {w w' : InfinitePlace L} (h : σ • w = w') : (D.act σ x).1 w' = transport σ h (x.1 w) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  rw [Subsingleton.elim D (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x h

variable {K L}

theorem comap_smul_algebraMap (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) :=
  InfinitePlace.ext _ _ fun x => by
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply, InfinitePlace.smul_apply, AlgEquiv.commutes]

theorem inv_smul_mem (σ : L ≃ₐ[K] L) {v : InfinitePlace K} (w : AFib K L v) : (σ⁻¹ • w.1).comap (algebraMap K L) = v :=
  (comap_smul_algebraMap σ⁻¹ w.1).trans w.2

def sh (σ : L ≃ₐ[K] L) {v : InfinitePlace K} (w : AFib K L v) : AFib K L v := ⟨σ⁻¹ • w.1, inv_smul_mem σ w⟩

theorem smul_sh (σ : L ≃ₐ[K] L) {v : InfinitePlace K} (w : AFib K L v) : σ • (sh σ w).1 = w.1 := smul_inv_smul σ w.1

section ext
variable {v : InfinitePlace K}

open Classical in

def ext1 (u : Π w : AFib K L v, w.1.Completion) : InfiniteAdeleRing L :=
  fun w => if h : w.comap (algebraMap K L) = v then u ⟨w, h⟩ else 1

open Classical in
theorem ext1_apply (u : Π w : AFib K L v, w.1.Completion) (w : AFib K L v) : ext1 u w.1 = u w := by
  obtain ⟨w, rfl⟩ := w
  show (if h : w.comap (algebraMap K L) = w.comap (algebraMap K L) then u ⟨w, h⟩ else 1) = u ⟨w, rfl⟩
  rw [dif_pos rfl]

end ext

section pinned
variable (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem _root_.P2mS26UnivA.phiA_apply
    (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (hΦa : ∀ (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (x : InfiniteAdeleRing L),
      (∀ w : AFib K L v, x w.1 = (u : Π w : AFib K L v, w.1.Completion) w) →
      ∀ w : AFib K L v, (D.act σ (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 w.1 = (Φa v u : Π w : AFib K L v, w.1.Completion) w)
    (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (w : AFib K L v) :
    (Φa v u : Π w : AFib K L v, w.1.Completion) w
      = transport σ (smul_sh σ w) ((u : Π w : AFib K L v, w.1.Completion) (sh σ w)) := by
  rw [← hΦa v u (ext1 (u : Π w : AFib K L v, w.1.Completion)) (ext1_apply _) w, act_coord K L D σ _ (smul_sh σ w)]
  show transport σ (smul_sh σ w) (ext1 (u : Π w : AFib K L v, w.1.Completion) (sh σ w).1) = _
  rw [ext1_apply]

p2m_export "P2mS26UnivA" "phiA_apply"
end pinned
end coord

section fibres
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev afplc {v : InfinitePlace K} {v0 : InfinitePlace (Shrink.{0} K)} (hv : iplc K v = v0) (w : AFib K L v) : AFib0 K L v0 :=
  ⟨iplc L w.1, by rw [comap_iplc, w.2, hv]⟩

abbrev afplcInv {v : InfinitePlace K} {v0 : InfinitePlace (Shrink.{0} K)} (hv : iplc K v = v0) (w0 : AFib0 K L v0) : AFib K L v :=
  ⟨(iplc L).symm w0.1, (iplc K).injective (by rw [← comap_iplc, Equiv.apply_symm_apply, w0.2, hv])⟩

variable {v : InfinitePlace K} {v0 : InfinitePlace (Shrink.{0} K)}

theorem iplc_afplcInv (hv : iplc K v = v0) (w0 : AFib0 K L v0) : iplc L (afplcInv (L := L) hv w0).1 = w0.1 :=
  Equiv.apply_symm_apply _ _

theorem afplc_afplcInv (hv : iplc K v = v0) (w0 : AFib0 K L v0) : afplc hv (afplcInv (L := L) hv w0) = w0 :=
  Subtype.ext (iplc_afplcInv hv w0)

theorem afplcInv_afplc (hv : iplc K v = v0) (w : AFib K L v) : afplcInv hv (afplc (L := L) hv w) = w :=
  Subtype.ext (Equiv.symm_apply_apply _ _)

def afibEquiv (hv : iplc K v = v0) : AFib K L v ≃ AFib0 K L v0 :=
  ⟨afplc hv, afplcInv hv, afplcInv_afplc hv, afplc_afplcInv hv⟩

theorem piA_aux1 (hv : iplc K v = v0) (u : Π w : AFib K L v, w.1.Completion) (w w' : AFib K L v) (e : w' = w)
    (h' : iplc L w'.1 = (afplc (L := L) hv w).1) :
    (icpl (rfl : iplc L w.1 = (afplc (L := L) hv w).1)).symm (icpl h' (u w')) = u w := by
  subst e; exact RingEquiv.symm_apply_apply _ _

theorem piA_aux2 (u0 : Π w0 : AFib0 K L v0, w0.1.Completion) (w0 w0' : AFib0 K L v0) (e : w0' = w0)
    (w : InfinitePlace L) (h : iplc L w = w0.1) (h' : iplc L w = w0'.1) :
    icpl h ((icpl h').symm (u0 w0')) = u0 w0 := by
  subst e; exact RingEquiv.apply_symm_apply _ _

set_option synthInstance.maxHeartbeats 800000 in

def piA (hv : iplc K v = v0) : (Π w : AFib K L v, w.1.Completion) ≃+* (Π w0 : AFib0 K L v0, w0.1.Completion) where
  toFun u w0 := icpl (iplc_afplcInv hv w0) (u (afplcInv hv w0))
  invFun u0 w := (icpl (rfl : iplc L w.1 = (afplc (L := L) hv w).1)).symm (u0 (afplc hv w))
  left_inv u := funext fun w => piA_aux1 hv u w _ (afplcInv_afplc hv w) _
  right_inv u0 := funext fun w0 => piA_aux2 u0 w0 _ (afplc_afplcInv hv w0) _ _ _
  map_mul' u u' := funext fun w0 => map_mul (icpl (iplc_afplcInv hv w0)) _ _
  map_add' u u' := funext fun w0 => map_add (icpl (iplc_afplcInv hv w0)) _ _

abbrev ΨA (hv : iplc K v = v0) : (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w0 : AFib0 K L v0, w0.1.Completion)ˣ :=
  Units.mapEquiv (piA hv).toMulEquiv

end fibres

section products
variable {K : Type uK} (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ihv0 (v0 : InfinitePlace (Shrink.{0} K)) : iplc K ((iplc K).symm v0) = v0 := Equiv.apply_symm_apply _ _

abbrev YA : Type _ := Π v : InfinitePlace K, (Π w : AFib K L v, w.1.Completion)ˣ
abbrev YA0 : Type := Π v0 : InfinitePlace (Shrink.{0} K), (Π w0 : AFib0 K L v0, w0.1.Completion)ˣ

theorem ΨY_aux1 (U : YA (K := K) L) (v v' : InfinitePlace K) (e : v' = v) (h' : iplc K v' = iplc K v) :
    (ΨA (L := L) (rfl : iplc K v = iplc K v)).symm (ΨA h' (U v')) = U v := by
  subst e; exact MulEquiv.symm_apply_apply _ _

theorem ΨY_aux2 (U0 : YA0 (K := K) L) (v0 v0' : InfinitePlace (Shrink.{0} K)) (e : v0' = v0)
    (v : InfinitePlace K) (h : iplc K v = v0) (h' : iplc K v = v0') :
    ΨA (L := L) h ((ΨA h').symm (U0 v0')) = U0 v0 := by
  subst e; exact MulEquiv.apply_symm_apply _ _

def ΨY : YA (K := K) L ≃* YA0 (K := K) L where
  toFun U v0 := ΨA (ihv0 v0) (U ((iplc K).symm v0))
  invFun U0 v := (ΨA (rfl : iplc K v = iplc K v)).symm (U0 (iplc K v))
  left_inv U := funext fun v => ΨY_aux1 L U v _ (Equiv.symm_apply_apply _ _) _
  right_inv U0 := funext fun v0 => ΨY_aux2 L U0 v0 _ (ihv0 v0) _ _ _
  map_mul' U U' := funext fun v0 => map_mul (ΨA (L := L) (ihv0 v0)) _ _

def ΘA : Additive (YA (K := K) L) ≃+ Additive (YA0 (K := K) L) := MulEquiv.toAdditive (ΨY L)

theorem ΘA_ofMul (U : YA (K := K) L) : ΘA L (Additive.ofMul U) = Additive.ofMul (ΨY L U) := rfl
theorem ΘA_symm_ofMul (U0 : YA0 (K := K) L) : (ΘA L).symm (Additive.ofMul U0) = Additive.ofMul ((ΨY L).symm U0) := rfl

def PhiA0 (Φa : (v : InfinitePlace K) → MulAut (Π w : AFib K L v, w.1.Completion)ˣ) (v0 : InfinitePlace (Shrink.{0} K)) :
    MulAut (Π w0 : AFib0 K L v0, w0.1.Completion)ˣ :=
  MulAut.congr (ΨA (ihv0 v0)) (Φa ((iplc K).symm v0))

theorem PhiA0_pow (Φa : (v : InfinitePlace K) → MulAut (Π w : AFib K L v, w.1.Completion)ˣ) (i : ℕ)
    (v0 : InfinitePlace (Shrink.{0} K)) : PhiA0 L (fun v => Φa v ^ i) v0 = PhiA0 L Φa v0 ^ i :=
  map_pow (MulAut.congr _) _ _

theorem ΨY_symm_aux (U0 : YA0 (K := K) L) (v0 v0' : InfinitePlace (Shrink.{0} K)) (e : v0' = v0)
    (v : InfinitePlace K) (h : iplc K v = v0) (h' : iplc K v = v0') :
    (ΨA (L := L) h').symm (U0 v0') = (ΨA h).symm (U0 v0) := by
  subst e; rfl

set_option maxHeartbeats 1600000 in

theorem ΨY_componentwise (Φa : (v : InfinitePlace K) → MulAut (Π w : AFib K L v, w.1.Completion)ˣ) (U0 : YA0 (K := K) L) :
    ΨY L ((fun v => Φa v (((ΨY L).symm U0) v)) : YA (K := K) L) = ((fun v0 => PhiA0 L Φa v0 (U0 v0)) : YA0 (K := K) L) := by
  funext v0
  show ΨA (ihv0 v0) (Φa ((iplc K).symm v0) ((ΨA (rfl : iplc K ((iplc K).symm v0) = iplc K ((iplc K).symm v0))).symm (U0 (iplc K ((iplc K).symm v0)))))
    = ΨA (ihv0 v0) (Φa ((iplc K).symm v0) ((ΨA (ihv0 v0)).symm (U0 v0)))
  rw [ΨY_symm_aux L U0 v0 _ (ihv0 v0) _ (ihv0 v0)]

end products

section descent
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
open NumberField.InfinitePlaceTransport

theorem transport_afib0_aux (τ : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) {v0 : InfinitePlace (Shrink.{0} K)}
    (u0 : Π w0 : AFib0 K L v0, w0.1.Completion) (w0 : AFib0 K L v0)
    (A B : AFib0 K L v0) (e : A = B) (hA : τ • A.1 = w0.1) (hB : τ • B.1 = w0.1) :
    transport τ hA (u0 A) = transport τ hB (u0 B) := by
  subst e; rfl

variable (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem afplc_sh {v : InfinitePlace K} {v0 : InfinitePlace (Shrink.{0} K)} (hv : iplc K v = v0) (w0 : AFib0 K L v0) :
    (afplc hv (sh σ (afplcInv (L := L) hv w0))).1 = (gal K L σ)⁻¹ • w0.1 := by
  show iplc L (σ⁻¹ • ((iplc L).symm w0.1)) = _
  rw [iplc_smul, gal_inv, Equiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in

theorem hPhiA0
    (Φa : (v : InfinitePlace K) → (Π w : AFib K L v, w.1.Completion)ˣ ≃* (Π w : AFib K L v, w.1.Completion)ˣ)
    (hΦa : ∀ (v : InfinitePlace K) (u : (Π w : AFib K L v, w.1.Completion)ˣ) (x : InfiniteAdeleRing L),
      (∀ w : AFib K L v, x w.1 = (u : Π w : AFib K L v, w.1.Completion) w) →
      ∀ w : AFib K L v, (D.act σ (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 w.1 = (Φa v u : Π w : AFib K L v, w.1.Completion) w)
    (v0 : InfinitePlace (Shrink.{0} K))
    (u0 : (Π w0 : AFib0 K L v0, w0.1.Completion)ˣ)
    (x0 : InfiniteAdeleRing (Shrink.{0} L))
    (hx : ∀ w0 : AFib0 K L v0, x0 w0.1 = (u0 : Π w0 : AFib0 K L v0, w0.1.Completion) w0)
    (w0 : AFib0 K L v0) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum (Shrink.{0} K) (Shrink.{0} L)).act (gal K L σ)
        (x0, (1 : FiniteAdeleRing (𝓞 (Shrink.{0} L)) (Shrink.{0} L)))).1 w0.1
      = (PhiA0 L Φa v0 u0 : Π w0 : AFib0 K L v0, w0.1.Completion) w0 := by
  have hsh0 : gal K L σ • ((gal K L σ)⁻¹ • w0.1) = w0.1 := smul_inv_smul _ _
  let sh0 : AFib0 K L v0 := ⟨(gal K L σ)⁻¹ • w0.1, (comap_smul_algebraMap _ w0.1).trans w0.2⟩
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply (Shrink.{0} K) (Shrink.{0} L) (gal K L σ) _ hsh0]
  have hx' : x0 ((gal K L σ)⁻¹ • w0.1) = (u0 : Π w0 : AFib0 K L v0, w0.1.Completion) sh0 := hx sh0
  have e : afplc (ihv0 v0) (sh σ (afplcInv (ihv0 v0) w0)) = sh0 := Subtype.ext (afplc_sh σ (ihv0 v0) w0)
  have h0' : gal K L σ • iplc L (sh σ (afplcInv (ihv0 v0) w0)).1 = w0.1 := by
    have := congrArg Subtype.val e
    rw [show iplc L (sh σ (afplcInv (ihv0 v0) w0)).1 = (afplc (ihv0 v0) (sh σ (afplcInv (ihv0 v0) w0))).1 from rfl, this]
    exact hsh0
  show transport (gal K L σ) hsh0 ((x0, (1 : FiniteAdeleRing (𝓞 (Shrink.{0} L)) (Shrink.{0} L))).1 ((gal K L σ)⁻¹ • w0.1))
    = icpl (iplc_afplcInv (ihv0 v0) w0) ((Φa ((iplc K).symm v0) ((ΨA (ihv0 v0)).symm u0) : Π w : AFib K L ((iplc K).symm v0), w.1.Completion) (afplcInv (ihv0 v0) w0))
  rw [phiA_apply σ D Φa hΦa ((iplc K).symm v0) _ (afplcInv (ihv0 v0) w0)]
  show transport (gal K L σ) hsh0 (x0 ((gal K L σ)⁻¹ • w0.1))
    = icpl (iplc_afplcInv (ihv0 v0) w0) (transport σ (smul_sh σ (afplcInv (ihv0 v0) w0))
        ((icpl (rfl : iplc L (sh σ (afplcInv (ihv0 v0) w0)).1 = iplc L (sh σ (afplcInv (ihv0 v0) w0)).1)).symm
          ((u0 : Π w0 : AFib0 K L v0, w0.1.Completion) (afplc (ihv0 v0) (sh σ (afplcInv (ihv0 v0) w0))))))
  rw [hx', icpl_transport σ (smul_sh σ (afplcInv (ihv0 v0) w0)) rfl (iplc_afplcInv (ihv0 v0) w0) h0', RingEquiv.apply_symm_apply]
  exact transport_afib0_aux (gal K L σ) (u0 : Π w0 : AFib0 K L v0, w0.1.Completion) w0 _ _ e.symm hsh0 h0'

end descent

section main
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L)
open NumberField.InfinitePlaceTransport

set_option maxHeartbeats 6400000 in

theorem hd0_of
    (Φa : (v : InfinitePlace K) → MulAut (Π w : AFib K L v, w.1.Completion)ˣ)
    (d : Additive (YA (K := K) L) →+ Additive (YA (K := K) L))
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul ((fun v => Φa v (u v))) - Additive.ofMul u)
    (d0 : Additive (YA0 (K := K) L) →+ Additive (YA0 (K := K) L))
    (hd' : ∀ a, d0 (ΘA L a) = ΘA L (d a)) (u0 : YA0 (K := K) L) :
    d0 (Additive.ofMul u0) = Additive.ofMul ((fun v0 => PhiA0 L Φa v0 (u0 v0))) - Additive.ofMul u0 := by
  have h := hd' ((ΘA L).symm (Additive.ofMul u0))
  rw [AddEquiv.apply_symm_apply] at h
  have hdU := hd ((ΨY L).symm u0)
  rw [h, ΘA_symm_ofMul, hdU, map_sub, ΘA_ofMul, ΘA_ofMul, MulEquiv.apply_symm_apply, ΨY_componentwise]

set_option maxHeartbeats 6400000 in

theorem hN0_of
    (Φa : (v : InfinitePlace K) → MulAut (Π w : AFib K L v, w.1.Completion)ˣ) (n : ℕ)
    (N : Additive (YA (K := K) L) →+ Additive (YA (K := K) L))
    (hN : ∀ u, N (Additive.ofMul u) = ∑ i ∈ Finset.range n, Additive.ofMul ((fun v => (Φa v ^ i) (u v))))
    (N0 : Additive (YA0 (K := K) L) →+ Additive (YA0 (K := K) L))
    (hN' : ∀ a, N0 (ΘA L a) = ΘA L (N a)) (u0 : YA0 (K := K) L) :
    N0 (Additive.ofMul u0) = ∑ i ∈ Finset.range n, Additive.ofMul ((fun v0 => (PhiA0 L Φa v0 ^ i) (u0 v0))) := by
  have h := hN' ((ΘA L).symm (Additive.ofMul u0))
  rw [AddEquiv.apply_symm_apply] at h
  have hNU := hN ((ΨY L).symm u0)
  rw [h, ΘA_symm_ofMul, hNU, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ΘA_ofMul]
  have h1 := ΨY_componentwise L (fun v => Φa v ^ i) u0
  simp only [PhiA0_pow] at h1
  exact congrArg Additive.ofMul h1

variable (K) in
theorem hsi0_of (si : InfinitePlace K → ℕ) (hsi : ∀ v, si v = Nat.card (AFib K L v)) (v0 : InfinitePlace (Shrink.{0} K)) :
    si ((iplc K).symm v0) = Nat.card (AFib0 K L v0) :=
  (hsi _).trans (Nat.card_congr (afibEquiv (L := L) (ihv0 v0)))

variable {L}

set_option maxHeartbeats 6400000 in

theorem descend
    (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (Φa : (v : InfinitePlace K) →
      (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ ≃*
      (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ)
    (hΦa : ∀ (v : InfinitePlace K)
      (u : (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ)
      (x : InfiniteAdeleRing L),
      (∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        x w.1 = (u : Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion) w) →
      ∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        (D.act σ (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 w.1 =
          (Φa v u : Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
            w.1.Completion) w)

    (d : Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ) →+
      Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φa v (u v))) - Additive.ofMul u)
    (N : Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ) →+
      Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φa v ^ i) (u v))))

    (si : InfinitePlace K → ℕ)
    (hsi : ∀ v, si v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / si v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  obtain ⟨d0, hd'⟩ := exists_conj (ΘA L (K := K)) d
  obtain ⟨N0, hN'⟩ := exists_conj (ΘA L (K := K)) N
  have hd0 := hd0_of L Φa d hd d0 (fun a => (hd' a).symm)
  have hN0 := hN0_of L Φa (Nat.card (L ≃ₐ[K] L)) N hN N0 (fun a => (hN' a).symm)
  rw [card_gal K L] at hN0
  have key := P2mS26GA.infiniteIdeleFibre_u0 (Shrink.{0} K) (Shrink.{0} L)
    (gal K L σ) (gal_generates K L hσ)
    (M4aHerbrand.GenuineDescent.genuineDescentDatum (Shrink.{0} K) (Shrink.{0} L))
    (PhiA0 L Φa) (fun v0 u0 x0 hx w0 => hPhiA0 σ D Φa hΦa v0 u0 x0 hx w0)
    d0 hd0 N0 hN0
    (fun v0 => si ((iplc K).symm v0)) (hsi0_of K L si hsi)
  refine ⟨?_, ?_⟩
  · rw [card_kerModRange_eq_of_addEquiv (ΘA L) d N d0 N0 hd' hN', key.1]
    symm
    refine Fintype.prod_equiv (iplc K) _ _ fun v => ?_
    rw [← card_gal, Equiv.symm_apply_apply]
  · rw [card_kerModRange_eq_of_addEquiv (ΘA L) N d N0 d0 hN' hd', key.2]

end main

end

end P2mS26UnivA

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (Φa : (v : InfinitePlace K) →
      (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ ≃*
      (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ)
    (hΦa : ∀ (v : InfinitePlace K)
      (u : (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        w.1.Completion)ˣ)
      (x : InfiniteAdeleRing L),
      (∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        x w.1 = (u : Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion) w) →
      ∀ w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
        (D.act σ (x, (1 : FiniteAdeleRing (𝓞 L) L))).1 w.1 =
          (Φa v u : Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
            w.1.Completion) w)

    (d : Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ) →+
      Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φa v (u v))) - Additive.ofMul u)
    (N : Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ) →+
      Additive (Π v : InfinitePlace K,
        (Π w : {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v},
          w.1.Completion)ˣ))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φa v ^ i) (u v))))

    (si : InfinitePlace K → ℕ)
    (hsi : ∀ v, si v = Nat.card {w : InfinitePlace L // InfinitePlace.comap w (algebraMap K L) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v : InfinitePlace K, Nat.card (L ≃ₐ[K] L) / si v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 :=
  P2mS26UnivA.descend K L σ hσ D Φa hΦa d hd N hN si hsi

end S_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd
end P2MW
export P2MW.S_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd (solution)
