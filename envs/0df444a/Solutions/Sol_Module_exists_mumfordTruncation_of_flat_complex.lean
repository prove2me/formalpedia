-- Prove2me | solution 1 for Module.exists_mumfordTruncation_of_flat_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/55640dfa-788c-56a0-ac3a-c309ba3ff696

import Mathlib
import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Theorems.Thm_TwoChartCech_Mumford_flat_K0
import Theorems.Thm_TwoChartCech_Mumford_finite_K0
import Theorems.Thm_TwoChartCech_Mumford_bijective_kerMapBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_mumfordTruncation_of_flat_complex

set_option autoImplicit false

universe u

open scoped TensorProduct

noncomputable section

namespace TwoChartCech
p2m_export "TwoChartCech" "Mumford.flat_K0 Mumford.finite_K0 Mumford.bijective_kerMapBaseChange kerMap"
namespace Mumford
p2m_export "TwoChartCech.Mumford" "rank lift surjective_coprod K0 mem_K0_iff dK ι0 ι1 ι1_eq comm flat_K0 finite_K0 bijective_kerMapBaseChange"
namespace NTerm
p2m_open "TwoChartCech.Mumford TwoChartCech"

section ThreeStep

variable {R : Type u} [CommRing R]
variable {C0 C1 C2 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup C2] [Module R C2]
variable (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hsq : d1 ∘ₗ d0 = 0)
variable [Module.Finite R (C2 ⧸ LinearMap.range d1)]

theorem subtype_baseChange_injective [Module.Flat R C2] (A : Type u) [CommRing A] [Algebra R A] :
    Function.Injective ((K0 d1).subtype.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_injective_of_exact_of_flat (d1.coprod (lift d1))
    (surjective_coprod d1) _ (K0 d1).subtype_injective (LinearMap.exact_subtype_ker_map _) A

theorem prodRight_apply_eq_baseChange (A : Type u) [CommRing A] [Algebra R A] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (w : A ⊗[R] (M × N)) :
    (TensorProduct.prodRight R A A M N) w
      = (((LinearMap.fst R M N).baseChange A) w, ((LinearMap.snd R M N).baseChange A) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact rfl
  | tmul a x => simp [TensorProduct.prodRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

theorem prodRight_subtype_baseChange (A : Type u) [CommRing A] [Algebra R A] (z : A ⊗[R] K0 d1) :
    (TensorProduct.prodRight R A A C1 (Fin (rank d1) → R)) (((K0 d1).subtype.baseChange A) z)
      = (((ι0 d1).baseChange A) z, ((dK d1).baseChange A) z) := by
  rw [prodRight_apply_eq_baseChange]
  refine Prod.ext ?_ ?_
  · show ((LinearMap.fst R C1 (Fin (rank d1) → R)).baseChange A) (((K0 d1).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl
  · show ((LinearMap.snd R C1 (Fin (rank d1) → R)).baseChange A) (((K0 d1).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl

theorem coprod_baseChange_apply (A : Type u) [CommRing A] [Algebra R A]
    (w : A ⊗[R] (C1 × (Fin (rank d1) → R))) :
    ((d1.coprod (lift d1)).baseChange A) w
      = (d1.baseChange A) ((TensorProduct.prodRight R A A C1 (Fin (rank d1) → R)) w).1
        + ((lift d1).baseChange A) ((TensorProduct.prodRight R A A C1 (Fin (rank d1) → R)) w).2 := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
  | tmul a x => simp [TensorProduct.prodRight_tmul, LinearMap.coprod_apply, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]; abel

def stepDiff : C0 →ₗ[R] K0 d1 :=
  LinearMap.codRestrict (K0 d1) ((LinearMap.inl R C1 _).comp d0)
    (fun y => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.coprod_apply,
        map_zero, add_zero, ← LinearMap.comp_apply, hsq, LinearMap.zero_apply])

theorem stepDiff_coe (y : C0) :
    ((stepDiff d0 d1 hsq y : K0 d1) : C1 × (Fin (rank d1) → R)) = (d0 y, 0) := rfl

theorem subtype_comp_stepDiff : (K0 d1).subtype ∘ₗ stepDiff d0 d1 hsq = (LinearMap.inl R C1 _) ∘ₗ d0 := rfl

theorem dK_comp_stepDiff : dK d1 ∘ₗ stepDiff d0 d1 hsq = 0 := by
  ext y; rfl

theorem stepDiff_ker : LinearMap.ker (stepDiff d0 d1 hsq) = LinearMap.ker d0 := by
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← (K0 d1).subtype_injective.eq_iff,
    Submodule.coe_subtype, stepDiff_coe, Submodule.coe_zero, Prod.mk_eq_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem stepDiff_ker_baseChange [Module.Flat R C2] (A : Type u) [CommRing A] [Algebra R A] :
    LinearMap.ker ((stepDiff d0 d1 hsq).baseChange A) = LinearMap.ker (d0.baseChange A) := by
  have hinl : Function.Injective ((LinearMap.inl R C1 (Fin (rank d1) → R)).baseChange A) := by
    apply Function.LeftInverse.injective (g := (LinearMap.fst R C1 (Fin (rank d1) → R)).baseChange A)
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.fst_comp_inl,
      LinearMap.baseChange_id, LinearMap.id_apply]
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← (subtype_baseChange_injective d1 A).eq_iff, map_zero,
    ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_stepDiff,
    LinearMap.baseChange_comp, LinearMap.comp_apply, ← hinl.eq_iff, map_zero]

theorem ker_dK_baseChange_le [Module.Flat R C2] (A : Type u) [CommRing A] [Algebra R A]
    (hA : LinearMap.ker (d1.baseChange A) ≤ LinearMap.range (d0.baseChange A)) :
    LinearMap.ker ((dK d1).baseChange A) ≤ LinearMap.range ((stepDiff d0 d1 hsq).baseChange A) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz

  have hcop : ((d1.coprod (lift d1)).baseChange A) (((K0 d1).subtype.baseChange A) z) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [coprod_baseChange_apply, prodRight_subtype_baseChange, hz, map_zero, add_zero] at hcop
  obtain ⟨y, hy⟩ := hA (LinearMap.mem_ker.mpr hcop)
  refine ⟨y, subtype_baseChange_injective d1 A ?_⟩
  apply (TensorProduct.prodRight R A A C1 (Fin (rank d1) → R)).injective
  rw [prodRight_subtype_baseChange, prodRight_subtype_baseChange, hz,
    ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    show ι0 d1 ∘ₗ stepDiff d0 d1 hsq = d0 from rfl, dK_comp_stepDiff, LinearMap.baseChange_zero,
    LinearMap.zero_apply, hy]

def kerToK0 : LinearMap.ker d1 →ₗ[R] K0 d1 :=
  LinearMap.codRestrict (K0 d1) ((LinearMap.inl R C1 _).comp (LinearMap.ker d1).subtype)
    (fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.coprod_apply, map_zero,
        add_zero, Submodule.coe_subtype]
      exact x.2)

theorem dK_comp_kerToK0 : dK d1 ∘ₗ kerToK0 d1 = 0 := by
  ext x; rfl

def h1ToCoker :
    (LinearMap.ker d1 ⧸ (LinearMap.range d0).comap (LinearMap.ker d1).subtype) →ₗ[R]
      (K0 d1 ⧸ LinearMap.range (stepDiff d0 d1 hsq)) :=
  Submodule.liftQ _ ((LinearMap.range (stepDiff d0 d1 hsq)).mkQ ∘ₗ kerToK0 d1)
    (by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext (Prod.ext hy rfl)⟩)

def cokerToFree : (K0 d1 ⧸ LinearMap.range (stepDiff d0 d1 hsq)) →ₗ[R] (Fin (rank d1) → R) :=
  Submodule.liftQ _ (dK d1) (by rintro _ ⟨y, rfl⟩; rfl)

theorem h1ToCoker_exact :
    LinearMap.range (h1ToCoker d0 d1 hsq) = LinearMap.ker (cokerToFree d0 d1 hsq) := by
  refine le_antisymm ?_ ?_
  · rw [LinearMap.range_le_ker_iff]
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, h1ToCoker, Submodule.liftQ_apply, cokerToFree,
      LinearMap.zero_comp, LinearMap.zero_apply]
    exact LinearMap.congr_fun (dK_comp_kerToK0 d1) x
  · rintro w hw
    obtain ⟨z, rfl⟩ := (LinearMap.range (stepDiff d0 d1 hsq)).mkQ_surjective w
    rw [LinearMap.mem_ker, cokerToFree, Submodule.mkQ_apply, Submodule.liftQ_apply] at hw
    rcases z with ⟨⟨x, v⟩, hxv⟩
    have hv : v = 0 := hw
    have hx : x ∈ LinearMap.ker d1 := by
      have hxv' : d1 x + lift d1 v = 0 := by
        have := (LinearMap.mem_ker).mp hxv; simpa [LinearMap.coprod_apply] using this
      rw [LinearMap.mem_ker]; simpa [hv, map_zero, add_zero] using hxv'
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    simp only [h1ToCoker, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    exact congrArg _ (Subtype.ext (Prod.ext rfl hv.symm))

variable [IsNoetherianRing R]

theorem stepDiff_coker_finite
    [Module.Finite R (LinearMap.ker d1 ⧸ (LinearMap.range d0).comap (LinearMap.ker d1).subtype)] :
    Module.Finite R (K0 d1 ⧸ LinearMap.range (stepDiff d0 d1 hsq)) := by
  haveI : Module.Finite R (LinearMap.ker (cokerToFree d0 d1 hsq)) := by
    rw [← h1ToCoker_exact]
    exact Module.Finite.range (h1ToCoker d0 d1 hsq)
  haveI : Module.Finite R ((K0 d1 ⧸ LinearMap.range (stepDiff d0 d1 hsq)) ⧸
      LinearMap.ker (cokerToFree d0 d1 hsq)) := by
    haveI : Module.Finite R (LinearMap.range (cokerToFree d0 d1 hsq)) := inferInstance
    exact Module.Finite.equiv (cokerToFree d0 d1 hsq).quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (cokerToFree d0 d1 hsq))

end ThreeStep

section Downward

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
variable (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
variable (hfin : ∀ i, Module.Finite R
    (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))

structure TruncInvariant (p : ℕ) where

  K : Type u
  [K_acg : AddCommGroup K]
  [K_mod : Module R K]
  [K_flat : Module.Flat R K]

  d' : C p →ₗ[R] K
  [coker_fin : Module.Finite R (K ⧸ LinearMap.range d')]
  hker : LinearMap.ker d' = LinearMap.ker (d p)
  hkerA : ∀ (A : Type u) [CommRing A] [Algebra R A],
    LinearMap.ker (d'.baseChange A) = LinearMap.ker ((d p).baseChange A)

attribute [scoped instance] TruncInvariant.K_acg TruncInvariant.K_mod TruncInvariant.K_flat TruncInvariant.coker_fin

def truncInvariantBase (N : ℕ) [Subsingleton (C (N + 1))] : TruncInvariant C d N where
  K := C (N + 1)
  d' := d N
  coker_fin := Module.Finite.of_surjective (LinearMap.range (d N)).mkQ (Submodule.mkQ_surjective _)
  hker := rfl
  hkerA := fun _ _ _ => rfl

include hdd hfin in

def truncInvariantStep (p : ℕ) (hP : TruncInvariant C d (p + 1)) : TruncInvariant C d p :=
  let hsq : hP.d' ∘ₗ d p = 0 := by
    ext y
    rw [LinearMap.comp_apply, LinearMap.zero_apply, ← LinearMap.mem_ker, hP.hker]
    exact LinearMap.ext_iff.mp (hdd p) y
  letI : Module.Finite R (LinearMap.ker hP.d' ⧸
      (LinearMap.range (d p)).comap (LinearMap.ker hP.d').subtype) := by
    haveI := hfin p
    refine Module.Finite.equiv
      (Submodule.Quotient.equiv
        ((LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
        ((LinearMap.range (d p)).comap (LinearMap.ker hP.d').subtype)
        (LinearEquiv.ofEq _ _ hP.hker.symm) ?_)
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    refine ⟨?_, fun ⟨y, hy⟩ => ⟨⟨x, hP.hker.symm ▸ hx⟩, ⟨y, hy⟩, rfl⟩⟩
    rintro ⟨⟨y, hy⟩, ⟨z, hz⟩, heq⟩
    exact ⟨z, hz.trans (congrArg Subtype.val heq)⟩
  { K := K0 hP.d'
    K_flat := TwoChartCech.Mumford.flat_K0 hP.d'
    d' := stepDiff (d p) hP.d' hsq
    coker_fin := stepDiff_coker_finite (d p) hP.d' hsq
    hker := stepDiff_ker (d p) hP.d' hsq
    hkerA := fun A _ _ => stepDiff_ker_baseChange (d p) hP.d' hsq A }

include hdd hfin in

def truncInvariantFrom (N : ℕ) [Subsingleton (C (N + 1))] (q : ℕ) (hq : q ≤ N) : TruncInvariant C d q :=
  Nat.decreasingInduction (motive := fun m _ => TruncInvariant C d m)
    (fun p _ hP => truncInvariantStep C d hdd hfin p hP)
    (truncInvariantBase C d N) hq

end Downward

section LastStep

variable {R : Type u} [CommRing R]
variable {C0 K1 F : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup F] [Module R F]
variable (δ : C0 →ₗ[R] K1) (ε : K1 →ₗ[R] F) (hεδ : ε ∘ₗ δ = 0)
variable [Module.Finite R (K1 ⧸ LinearMap.range δ)]

def epsK : (Fin (rank δ) → R) →ₗ[R] F := ε ∘ₗ ι1 δ

include hεδ in
theorem epsK_comp_dK : epsK δ ε ∘ₗ dK δ = 0 := by
  rw [epsK, LinearMap.comp_assoc, ← comm δ, ← LinearMap.comp_assoc, hεδ, LinearMap.zero_comp]

theorem mem_range_subtype_baseChange (A : Type u) [CommRing A] [Algebra R A]
    (w : A ⊗[R] (C0 × (Fin (rank δ) → R))) :
    ((δ.coprod (lift δ)).baseChange A) w = 0 ↔ ∃ z, ((K0 δ).subtype.baseChange A) z = w := by
  have heqι : ⇑((K0 δ).subtype.baseChange A) = ⇑((K0 δ).subtype.lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  have heqc : ⇑((δ.coprod (lift δ)).baseChange A) = ⇑((δ.coprod (lift δ)).lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  rw [heqc]
  simp only [heqι]
  exact lTensor_exact A (LinearMap.exact_subtype_ker_map _) (surjective_coprod δ) w

theorem ker_epsK_baseChange_le (A : Type u) [CommRing A] [Algebra R A]
    (hA : LinearMap.ker (ε.baseChange A) ≤ LinearMap.range (δ.baseChange A)) :
    LinearMap.ker ((epsK δ ε).baseChange A) ≤ LinearMap.range ((dK δ).baseChange A) := by
  intro v hv
  rw [LinearMap.mem_ker, epsK, LinearMap.baseChange_comp, LinearMap.comp_apply] at hv
  obtain ⟨x, hx⟩ := hA (LinearMap.mem_ker.mpr hv)

  let w : A ⊗[R] (C0 × (Fin (rank δ) → R)) := (TensorProduct.prodRight R A A C0 (Fin (rank δ) → R)).symm (x, v)
  have hw : (TensorProduct.prodRight R A A C0 (Fin (rank δ) → R)) w = (x, v) := LinearEquiv.apply_symm_apply _ _
  have hker : ((δ.coprod (lift δ)).baseChange A) w = 0 := by
    rw [coprod_baseChange_apply, hw, hx]
    show ((ι1 δ).baseChange A) v + ((lift δ).baseChange A) v = 0
    rw [ι1_eq, LinearMap.baseChange_neg, LinearMap.neg_apply, neg_add_cancel]
  obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange δ A w).mp hker
  refine ⟨z, ?_⟩
  have := congrArg (fun p => ((TensorProduct.prodRight R A A C0 (Fin (rank δ) → R)) p).2) hz
  simp only [prodRight_subtype_baseChange, hw] at this
  exact this

theorem kerMap_bijective : Function.Bijective (kerMap (dK δ) δ (ι0 δ) (ι1 δ) (comm δ)) := by
  constructor
  · rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩ ⟨⟨⟨x', v'⟩, hxv'⟩, hv'⟩ h
    have hv0 : v = 0 := LinearMap.mem_ker.mp hv
    have hv0' : v' = 0 := LinearMap.mem_ker.mp hv'
    have hx : x = x' := congrArg Subtype.val h
    subst hv0; subst hv0'; subst hx
    rfl
  · rintro ⟨x, hx⟩
    refine ⟨⟨⟨(x, 0), (mem_K0_iff δ _).mpr (by rw [LinearMap.mem_ker.mp hx, map_zero, add_zero])⟩,
      LinearMap.mem_ker.mpr rfl⟩, rfl⟩

def kerMapEquiv : LinearMap.ker (dK δ) ≃ₗ[R] LinearMap.ker δ := LinearEquiv.ofBijective _ (kerMap_bijective δ)

theorem subtype_comp_kerMap :
    (LinearMap.ker δ).subtype ∘ₗ kerMap (dK δ) δ (ι0 δ) (ι1 δ) (comm δ) = ι0 δ ∘ₗ (LinearMap.ker (dK δ)).subtype :=
  LinearMap.ext fun _ => rfl

variable [Module.Flat R K1]

theorem range_subtype_baseChange_eq_ker (A : Type u) [CommRing A] [Algebra R A]
    (h : LinearMap.range ((LinearMap.ker (dK δ)).subtype.baseChange A) = LinearMap.ker ((dK δ).baseChange A)) :
    LinearMap.range ((LinearMap.ker δ).subtype.baseChange A) = LinearMap.ker (δ.baseChange A) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  · intro x hx
    obtain ⟨z, hz⟩ := (TwoChartCech.Mumford.bijective_kerMapBaseChange δ A).2 ⟨x, hx⟩
    have hzx : ((ι0 δ).baseChange A) (z : A ⊗[R] K0 δ) = x := congrArg Subtype.val hz
    have hz1 : (z : A ⊗[R] K0 δ) ∈ LinearMap.range ((LinearMap.ker (dK δ)).subtype.baseChange A) := by
      rw [h]; exact z.2
    obtain ⟨w, hw⟩ := hz1
    refine ⟨(kerMap (dK δ) δ (ι0 δ) (ι1 δ) (comm δ)).baseChange A w, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_kerMap, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hw, hzx]

theorem subtype_baseChange_injective_of (A : Type u) [CommRing A] [Algebra R A]
    (h : Function.Injective ((LinearMap.ker (dK δ)).subtype.baseChange A)) :
    Function.Injective ((LinearMap.ker δ).subtype.baseChange A) := by
  let e := kerMapEquiv δ

  have hsq : ⇑((LinearMap.ker δ).subtype.baseChange A) ∘ ⇑(e.toLinearMap.baseChange A)
      = ⇑((ι0 δ).baseChange A) ∘ ⇑((LinearMap.ker (dK δ)).subtype.baseChange A) := by
    funext w
    show ((LinearMap.ker δ).subtype.baseChange A) ((kerMap (dK δ) δ (ι0 δ) (ι1 δ) (comm δ)).baseChange A w) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_kerMap, LinearMap.baseChange_comp,
      LinearMap.comp_apply]
    rfl
  have hrhs : Function.Injective (⇑((ι0 δ).baseChange A) ∘ ⇑((LinearMap.ker (dK δ)).subtype.baseChange A)) := by
    intro a b hab
    have ha : ((LinearMap.ker (dK δ)).subtype.baseChange A) a ∈ LinearMap.ker ((dK δ).baseChange A) := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype,
        LinearMap.baseChange_zero, LinearMap.zero_apply]
    have hb : ((LinearMap.ker (dK δ)).subtype.baseChange A) b ∈ LinearMap.ker ((dK δ).baseChange A) := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype,
        LinearMap.baseChange_zero, LinearMap.zero_apply]
    have hinj := (TwoChartCech.Mumford.bijective_kerMapBaseChange δ A).1
      (a₁ := ⟨_, ha⟩) (a₂ := ⟨_, hb⟩) (Subtype.ext hab)
    exact h (congrArg Subtype.val hinj)
  have h1 : (e.symm.toLinearMap.baseChange A) ∘ₗ (e.toLinearMap.baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp,
      show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from LinearMap.ext e.symm_apply_apply,
      LinearMap.baseChange_id]
  have h2 : (e.toLinearMap.baseChange A) ∘ₗ (e.symm.toLinearMap.baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp,
      show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from LinearMap.ext e.apply_symm_apply,
      LinearMap.baseChange_id]
  have he : Function.Bijective ⇑(e.toLinearMap.baseChange A) :=
    (LinearEquiv.ofLinear (e.toLinearMap.baseChange A) (e.symm.toLinearMap.baseChange A) h2 h1 :
      A ⊗[R] LinearMap.ker (dK δ) ≃ₗ[A] A ⊗[R] LinearMap.ker δ).bijective
  have hcomp : Function.Injective (⇑((LinearMap.ker δ).subtype.baseChange A) ∘ ⇑(e.toLinearMap.baseChange A)) := by
    rw [hsq]; exact hrhs
  exact (Function.Injective.of_comp_iff' _ he).mp hcomp

end LastStep

section FinalStep

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C0 C1 C2 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup C2] [Module R C2] [Module.Flat R C0] [Module.Flat R C1] [Module.Flat R C2]
variable (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hsq : d1 ∘ₗ d0 = 0)
variable [Module.Finite R (C2 ⧸ LinearMap.range d1)]
variable [Module.Finite R (LinearMap.ker d1 ⧸ (LinearMap.range d0).comap (LinearMap.ker d1).subtype)]

set_option maxHeartbeats 1600000 in
include hsq in
theorem finalStep (hfin0 : Module.Finite R (LinearMap.ker d0)) :
    ∃ (m₀ m₁ : ℕ) (P : Submodule R (C0 × (Fin m₀ → R))) (ε : (Fin m₀ → R) →ₗ[R] (Fin m₁ → R)),
      Module.Finite R P ∧ Module.Flat R P ∧
      ε ∘ₗ (LinearMap.snd R C0 (Fin m₀ → R) ∘ₗ P.subtype) = 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (LinearMap.ker (d1.baseChange A) ≤ LinearMap.range (d0.baseChange A) →
          LinearMap.ker (ε.baseChange A)
            ≤ LinearMap.range ((LinearMap.snd R C0 (Fin m₀ → R) ∘ₗ P.subtype).baseChange A)) ∧
        (LinearMap.range ((LinearMap.ker (LinearMap.snd R C0 (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A)
            = LinearMap.ker ((LinearMap.snd R C0 (Fin m₀ → R) ∘ₗ P.subtype).baseChange A) →
          LinearMap.range ((LinearMap.ker d0).subtype.baseChange A) = LinearMap.ker (d0.baseChange A)) ∧
        (Function.Injective
            ((LinearMap.ker (LinearMap.snd R C0 (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A) →
          Function.Injective ((LinearMap.ker d0).subtype.baseChange A)) := by

  haveI : Module.Finite R (K0 d1 ⧸ LinearMap.range (stepDiff d0 d1 hsq)) := stepDiff_coker_finite d0 d1 hsq
  haveI : Module.Flat R (K0 d1) := TwoChartCech.Mumford.flat_K0 d1
  have hkerδ : LinearMap.ker (stepDiff d0 d1 hsq) = LinearMap.ker d0 := stepDiff_ker d0 d1 hsq
  haveI : Module.Finite R (LinearMap.ker (stepDiff d0 d1 hsq)) := hkerδ ▸ hfin0
  have hεδ : dK d1 ∘ₗ stepDiff d0 d1 hsq = 0 := dK_comp_stepDiff d0 d1 hsq

  have hsubR : ∀ (A : Type u) [CommRing A] [Algebra R A],
      LinearMap.range ((LinearMap.ker (stepDiff d0 d1 hsq)).subtype.baseChange A)
        = LinearMap.range ((LinearMap.ker d0).subtype.baseChange A) := by
    intro A _ _
    have key : ∀ (N N' : Submodule R C0), N = N' →
        LinearMap.range (N.subtype.baseChange A) = LinearMap.range (N'.subtype.baseChange A) := by
      rintro N _ rfl; rfl
    exact key _ _ hkerδ
  have hsubI : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Injective ((LinearMap.ker (stepDiff d0 d1 hsq)).subtype.baseChange A) →
        Function.Injective ((LinearMap.ker d0).subtype.baseChange A) := by
    intro A _ _
    have key : ∀ (N N' : Submodule R C0), N = N' →
        Function.Injective (N.subtype.baseChange A) → Function.Injective (N'.subtype.baseChange A) := by
      rintro N _ rfl h; exact h
    exact key _ _ hkerδ

  refine ⟨rank (stepDiff d0 d1 hsq), rank d1, K0 (stepDiff d0 d1 hsq), epsK (stepDiff d0 d1 hsq) (dK d1),
    TwoChartCech.Mumford.finite_K0 _, TwoChartCech.Mumford.flat_K0 _,
    epsK_comp_dK (stepDiff d0 d1 hsq) (dK d1) hεδ, fun A _ _ => ⟨fun hA => ?_, fun h => ?_, fun h => ?_⟩⟩
  · have h2 : LinearMap.ker ((dK d1).baseChange A) ≤ LinearMap.range ((stepDiff d0 d1 hsq).baseChange A) :=
      ker_dK_baseChange_le d0 d1 hsq A hA
    exact ker_epsK_baseChange_le (stepDiff d0 d1 hsq) (dK d1) A h2
  · have h' : LinearMap.range ((LinearMap.ker (stepDiff d0 d1 hsq)).subtype.baseChange A)
        = LinearMap.ker ((stepDiff d0 d1 hsq).baseChange A) :=
      range_subtype_baseChange_eq_ker (stepDiff d0 d1 hsq) A h
    rw [hsubR A, stepDiff_ker_baseChange d0 d1 hsq A] at h'
    exact h'
  · exact hsubI A (subtype_baseChange_injective_of (stepDiff d0 d1 hsq) A h)

end FinalStep

end TwoChartCech.Mumford.NTerm
p2m_reactivate "P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech.Mumford P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech.Mumford.NTerm"
p2m_reactivate "P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech.Mumford"
p2m_reactivate "P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech"

end
p2m_reactivate "P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech.Mumford P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech.Mumford.NTerm"

set_option maxHeartbeats 1600000 in
open _root_.TwoChartCech.Mumford _root_.P2MW.S_Module_exists_mumfordTruncation_of_flat_complex.TwoChartCech.Mumford TwoChartCech.Mumford.NTerm in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (m₀ m₁ : ℕ) (P : Submodule R (C 0 × (Fin m₀ → R))) (ε : (Fin m₀ → R) →ₗ[R] (Fin m₁ → R)),
      Module.Finite R P ∧ Module.Flat R P ∧
      ε ∘ₗ (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype) = 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (LinearMap.ker ((d 1).baseChange A) ≤ LinearMap.range ((d 0).baseChange A) →
          LinearMap.ker (ε.baseChange A)
            ≤ LinearMap.range ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A)) ∧
        (LinearMap.range ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A)
            = LinearMap.ker ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A) →
          LinearMap.range ((LinearMap.ker (d 0)).subtype.baseChange A) = LinearMap.ker ((d 0).baseChange A)) ∧
        (Function.Injective
            ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A) →
          Function.Injective ((LinearMap.ker (d 0)).subtype.baseChange A)) := by

  haveI : Subsingleton (C (max n 1 + 1)) := hbdd _ (Nat.lt_succ_of_le (le_max_left n 1))
  let T : TruncInvariant C d 1 := truncInvariantFrom C d hdd hfin (max n 1) 1 (le_max_right n 1)

  have hsq : T.d' ∘ₗ d 0 = 0 := by
    ext y
    rw [LinearMap.comp_apply, LinearMap.zero_apply, ← LinearMap.mem_ker, T.hker]
    exact LinearMap.ext_iff.mp (hdd 0) y
  haveI : Module.Finite R (LinearMap.ker T.d' ⧸ (LinearMap.range (d 0)).comap (LinearMap.ker T.d').subtype) := by
    haveI := hfin 0
    refine Module.Finite.equiv
      (Submodule.Quotient.equiv
        ((LinearMap.range (d 0)).comap (LinearMap.ker (d (0 + 1))).subtype)
        ((LinearMap.range (d 0)).comap (LinearMap.ker T.d').subtype)
        (LinearEquiv.ofEq _ _ T.hker.symm) ?_)
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    refine ⟨?_, fun ⟨y, hy⟩ => ⟨⟨x, T.hker.symm ▸ hx⟩, ⟨y, hy⟩, rfl⟩⟩
    rintro ⟨⟨y, hy⟩, ⟨z, hz⟩, heq⟩
    exact ⟨z, hz.trans (congrArg Subtype.val heq)⟩
  obtain ⟨m₀, m₁, P, ε, hPf, hPl, hεδ, h⟩ := finalStep (d 0) T.d' hsq hfin0
  refine ⟨m₀, m₁, P, ε, hPf, hPl, hεδ, fun A _ _ => ⟨fun hA => (h A).1 ?_, (h A).2.1, (h A).2.2⟩⟩
  rw [T.hkerA A]
  exact hA

end S_Module_exists_mumfordTruncation_of_flat_complex
end P2MW
export P2MW.S_Module_exists_mumfordTruncation_of_flat_complex (solution)
