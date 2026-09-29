-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e3f3d1a6-546a-5747-b134-d47d57183f66

import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_laurentPolynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle"
namespace HSTAV
p2m_open "GoodReductionJacobian"

variable {k : Type u} [Field k]

section algebra

variable {t : ℕ}

def vGE (i : ℕ) (v : Fin t → ℤ) : Fin t → ℤ := fun j => if i ≤ (j : ℕ) then v j else 0

theorem vGE_add (i : ℕ) (v w : Fin t → ℤ) : vGE i (v + w) = vGE i v + vGE i w := by
  funext j; simp only [vGE, Pi.add_apply]; split_ifs <;> simp

theorem vGE_zero (i : ℕ) : vGE i (0 : Fin t → ℤ) = 0 := by
  funext j; simp [vGE]

theorem vGE_zero_left (v : Fin t → ℤ) : vGE 0 v = v := by
  funext j; simp [vGE]

theorem vGE_of_le (i : ℕ) (hi : t ≤ i) (v : Fin t → ℤ) : vGE i v = 0 := by
  funext j; simp only [vGE, Pi.zero_apply]; rw [if_neg]; omega

theorem vGE_eq_succ_add (i : Fin t) (v : Fin t → ℤ) :
    vGE (i : ℕ) v = vGE ((i : ℕ) + 1) v + Pi.single i (v i) := by
  funext j
  simp only [vGE, Pi.add_apply]
  by_cases hji : j = i
  · subst hji; simp
  · rw [Pi.single_eq_of_ne hji]
    have : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h).symm
    by_cases h1 : (i : ℕ) ≤ (j : ℕ)
    · have h2 : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
      simp [h1, h2]
    · have h2 : ¬ (i : ℕ) + 1 ≤ (j : ℕ) := by omega
      simp [h1, h2]

def trunc (F : Multiplicative (Fin t → ℤ) →* k) (i : ℕ) : Multiplicative (Fin t → ℤ) →* k where
  toFun v := F (Multiplicative.ofAdd (vGE i (Multiplicative.toAdd v)))
  map_one' := by rw [toAdd_one, vGE_zero, ofAdd_zero, map_one]
  map_mul' v w := by rw [toAdd_mul, vGE_add, ofAdd_add, map_mul]

theorem trunc_apply (F : Multiplicative (Fin t → ℤ) →* k) (i : ℕ) (v : Fin t → ℤ) :
    trunc F i (Multiplicative.ofAdd v) = F (Multiplicative.ofAdd (vGE i v)) := rfl

theorem trunc_zero (F : Multiplicative (Fin t → ℤ) →* k) : trunc F 0 = F := by
  ext v; simp [trunc, vGE_zero_left]

theorem trunc_of_le (F : Multiplicative (Fin t → ℤ) →* k) (i : ℕ) (hi : t ≤ i) : trunc F i = 1 := by
  ext v; simp [trunc, vGE_of_le i hi]

def curve (F : Multiplicative (Fin t → ℤ) →* k) (i : Fin t) :
    Multiplicative (Fin t → ℤ) →* LaurentPolynomial k where
  toFun v := AddMonoidAlgebra.single (Multiplicative.toAdd v i) (trunc F ((i : ℕ) + 1) v)
  map_one' := by rw [toAdd_one, Pi.zero_apply, map_one]; rfl
  map_mul' v w := by
    show AddMonoidAlgebra.single ((Multiplicative.toAdd v + Multiplicative.toAdd w) i) (trunc F ((i : ℕ) + 1) (v * w)) = _
    rw [(trunc F ((i : ℕ) + 1)).map_mul, Pi.add_apply]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

theorem lift_curve_single (F : Multiplicative (Fin t → ℤ) →* k) (i : Fin t) (v : Fin t → ℤ) :
    AddMonoidAlgebra.lift k (LaurentPolynomial k) (Fin t → ℤ) (curve F i) (AddMonoidAlgebra.single v 1) =
      AddMonoidAlgebra.single (v i) (F (Multiplicative.ofAdd (vGE ((i : ℕ) + 1) v))) := by
  rw [AddMonoidAlgebra.lift_single, one_smul]; rfl

def ev (u : kˣ) : LaurentPolynomial k →ₐ[k] k :=
  AddMonoidAlgebra.lift k k ℤ ((Units.coeHom k).comp (zpowersHom kˣ u))

theorem ev_single (u : kˣ) (n : ℤ) (a : k) :
    ev u (AddMonoidAlgebra.single n a) = a * ((u ^ n : kˣ) : k) := by
  show AddMonoidAlgebra.lift k k ℤ _ (AddMonoidAlgebra.single n a) = _
  rw [AddMonoidAlgebra.lift_single]
  simp

theorem ev_comp_lift_curve_eq_trunc (F : Multiplicative (Fin t → ℤ) →* k) (i : Fin t) :
    (ev (F.toHomUnits (Multiplicative.ofAdd (Pi.single i 1)))).comp
        (AddMonoidAlgebra.lift k (LaurentPolynomial k) (Fin t → ℤ) (curve F i)) =
      AddMonoidAlgebra.lift k k (Fin t → ℤ) (trunc F i) := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, lift_curve_single, ev_single, AddMonoidAlgebra.lift_single, one_smul,
    trunc_apply, vGE_eq_succ_add i v, ofAdd_add, map_mul]
  congr 1
  rw [Units.val_zpow_eq_zpow_val, MonoidHom.coe_toHomUnits, ← map_zpow, ← ofAdd_zsmul]
  congr 2
  rw [← Pi.single_smul', smul_eq_mul, mul_one]

theorem ev_one_comp_lift_curve (F : Multiplicative (Fin t → ℤ) →* k) (i : Fin t) :
    (ev 1).comp (AddMonoidAlgebra.lift k (LaurentPolynomial k) (Fin t → ℤ) (curve F i)) =
      AddMonoidAlgebra.lift k k (Fin t → ℤ) (trunc F ((i : ℕ) + 1)) := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, lift_curve_single, ev_single, AddMonoidAlgebra.lift_single, one_smul,
    one_zpow, Units.val_one, mul_one, trunc_apply]

end algebra

section geometry

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} {t : ℕ}
  (φ : Spec (CommRingCat.of (AddMonoidAlgebra k (Fin t → ℤ))) ⟶ A)

def P (χ : AddMonoidAlgebra k (Fin t → ℤ) →ₐ[k] k) : A :=
  (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ φ) (IsLocalRing.closedPoint k)

variable (hA : AbelianSchemePropertyBundle k f)
  (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ)))))
include hA hφ

theorem P_ev_comp_eq (c : AddMonoidAlgebra k (Fin t → ℤ) →ₐ[k] LaurentPolynomial k) (u u' : kˣ) :
    P φ ((ev u).comp c) = P φ ((ev u').comp c) := by
  have hψ : (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ φ) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) := by
    rw [Category.assoc, hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact c.comp_algebraMap
  obtain ⟨b, -, hb⟩ := hA.exists_eq_comp_of_hom_spec_laurentPolynomial _ hψ
  have key : ∀ w : kˣ, P φ ((ev w).comp c) = b (IsLocalRing.closedPoint k) := by
    intro w
    have e : Spec.map (CommRingCat.ofHom ((ev w).comp c).toRingHom) ≫ φ =
        Spec.map (CommRingCat.ofHom (ev w).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) ≫ b := by
      rw [← hb, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    unfold P
    rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  rw [key, key]

theorem P_trunc_succ (F : Multiplicative (Fin t → ℤ) →* k) (i : Fin t) :
    P φ (AddMonoidAlgebra.lift k k (Fin t → ℤ) (trunc F (i : ℕ))) =
      P φ (AddMonoidAlgebra.lift k k (Fin t → ℤ) (trunc F ((i : ℕ) + 1))) := by
  rw [← ev_comp_lift_curve_eq_trunc, ← ev_one_comp_lift_curve]
  exact P_ev_comp_eq φ hA hφ _ _ _

theorem P_trunc_eq : ∀ (F : Multiplicative (Fin t → ℤ) →* k) (i : ℕ), i ≤ t →
    P φ (AddMonoidAlgebra.lift k k (Fin t → ℤ) (trunc F 0)) =
      P φ (AddMonoidAlgebra.lift k k (Fin t → ℤ) (trunc F i))
  | _, 0, _ => rfl
  | F, i + 1, h => (P_trunc_eq F i (Nat.le_of_succ_le h)).trans (P_trunc_succ φ hA hφ F ⟨i, h⟩)

theorem P_lift_eq (F : Multiplicative (Fin t → ℤ) →* k) :
    P φ (AddMonoidAlgebra.lift k k (Fin t → ℤ) F) = P φ (AddMonoidAlgebra.lift k k (Fin t → ℤ) 1) := by
  have h := P_trunc_eq φ hA hφ F t le_rfl
  rwa [trunc_zero, trunc_of_le F t le_rfl] at h

theorem main [IsAlgClosed k] : ∃ a : Spec (CommRingCat.of k) ⟶ A, a ≫ f = 𝟙 _ ∧
    φ = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ)))) ≫ a := by
  set R := AddMonoidAlgebra k (Fin t → ℤ) with hR
  set str := Spec.map (CommRingCat.ofHom (algebraMap k R)) with hstr
  let ε : R →ₐ[k] k := AddMonoidAlgebra.lift k k (Fin t → ℤ) 1
  have hε : Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ str = 𝟙 _ := by
    rw [hstr, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : ε.toRingHom.comp (algebraMap k R) = RingHom.id k := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  refine ⟨Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ φ, by rw [Category.assoc, hφ, hε], ?_⟩

  have := hA.proper
  have := hA.smooth
  have hlft : LocallyOfFiniteType str := by
    rw [hstr, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : LocallyOfFiniteType (φ ≫ f) := by rw [hφ]; exact hlft
  refine ext_of_apply_eq f Set.univ isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_)
    (by rw [Category.assoc, Category.assoc, hφ, hε, Category.comp_id])

  have hp := pointOfClosedPoint_comp str x hx
  set p := pointOfClosedPoint str x hx with hpdef
  have hcomp : (Spec.preimage p).hom.comp (algebraMap k R) = RingHom.id k := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap k R) ≫ Spec.preimage p) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]; exact hp
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  let χ : R →ₐ[k] k :=
    { (Spec.preimage p).hom with
      commutes' := fun r => by
        have := RingHom.congr_fun hcomp r
        simpa using this }
  have hχ : Spec.map (CommRingCat.ofHom χ.toRingHom) = p := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage p).hom) = p
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]

  have lhs : φ x = P φ χ := by
    unfold P
    rw [hχ, Scheme.Hom.comp_apply, hpdef, pointOfClosedPoint_apply]

  have rhs : (str ≫ Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ φ) x = P φ ε := by
    unfold P
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    exact congrArg _ (Subsingleton.elim _ _)
  rw [lhs, rhs]

  obtain ⟨F, hF⟩ : ∃ F, AddMonoidAlgebra.lift k k (Fin t → ℤ) F = χ := ⟨_, Equiv.apply_symm_apply _ χ⟩
  rw [← hF]
  exact P_lift_eq φ hA hφ F

end geometry

end GoodReductionJacobian.HSTAV

end

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f) (t : ℕ)
    (φ : Spec (CommRingCat.of (AddMonoidAlgebra k (Fin t → ℤ))) ⟶ A)
    (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ))))) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A, a ≫ f = 𝟙 _ ∧
      φ = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ)))) ≫ a := by
  exact GoodReductionJacobian.HSTAV.main φ hA hφ

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int (solution)
