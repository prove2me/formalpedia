-- Prove2me | solution 1 for ModularCurve.FullLevel.ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e81fe7cb-6f5c-50e8-ba0e-c8404f6626f6

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization
import Theorems.Thm_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm
import Theorems.Thm_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

namespace InvHspanSol

section FiniteGroup

open CuspidalType

variable {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem unipotent_mul (s t : ZMod q) : unipotent q s * unipotent q t = unipotent q (s + t) := by
  apply Units.ext
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

variable (ρ : Representation K (GL2 q) V)

noncomputable def uniSum : V →ₗ[K] V := ∑ t : ZMod q, ρ (unipotent q t)

theorem uniSum_apply (v : V) : uniSum ρ v = ∑ t : ZMod q, ρ (unipotent q t) v := by
  simp [uniSum, LinearMap.sum_apply]

theorem rho_unipotent_uniSum (s : ZMod q) (v : V) :
    ρ (unipotent q s) (uniSum ρ v) = uniSum ρ v := by
  rw [uniSum_apply, map_sum]
  have h : ∀ t : ZMod q, ρ (unipotent q s) (ρ (unipotent q t) v) = ρ (unipotent q (s + t)) v := by
    intro t
    rw [← unipotent_mul, map_mul, Module.End.mul_apply]
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun t => rfl)

theorem uniSum_uniSum (v : V) : uniSum ρ (uniSum ρ v) = (q : K) • uniSum ρ v := by
  rw [uniSum_apply ρ (uniSum ρ v)]
  simp_rw [rho_unipotent_uniSum]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul K]

theorem uniSum_of_fixed {v : V} (hv : ∀ t : ZMod q, ρ (unipotent q t) v = v) :
    uniSum ρ v = (q : K) • v := by
  rw [uniSum_apply]
  simp_rw [hv]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul K]

theorem sum_mul_apply (g : GL2 q) (v : V) :
    (∑ t : ZMod q, ρ (unipotent q t) * ρ g) v = uniSum ρ (ρ g v) := by
  rw [← Finset.sum_mul, Module.End.mul_apply]
  rfl

def cusp : Submodule K V where
  carrier := {v | ∀ g : GL2 q, uniSum ρ (ρ g v) = 0}
  zero_mem' := by
    intro g
    simp
  add_mem' := by
    intro a b ha hb g
    simp only [Set.mem_setOf_eq] at ha hb
    simp [map_add, ha g, hb g]
  smul_mem' := by
    intro c v hv g
    simp only [Set.mem_setOf_eq] at hv
    simp [map_smul, hv g]

theorem cusp_stable (g : GL2 q) {v : V} (hv : v ∈ cusp ρ) : ρ g v ∈ cusp ρ := by
  intro h
  have h1 : ρ h (ρ g v) = ρ (h * g) v := by
    rw [map_mul, Module.End.mul_apply]
  rw [h1]
  exact hv (h * g)

def eisSet : Set V := {x | ∃ (g : GL2 q) (w : V), x = ρ g (uniSum ρ w)}

def eis : Submodule K V := Submodule.span K (eisSet ρ)

theorem uniSum_mem_eis (w : V) : uniSum ρ w ∈ eis ρ :=
  Submodule.subset_span ⟨1, w, by simp⟩

theorem rho_uniSum_mem_eis (g : GL2 q) (w : V) : ρ g (uniSum ρ w) ∈ eis ρ :=
  Submodule.subset_span ⟨g, w, rfl⟩

theorem eis_stable (g : GL2 q) {v : V} (hv : v ∈ eis ρ) : ρ g v ∈ eis ρ := by
  have hle : (eis ρ).map (ρ g) ≤ eis ρ := by
    rw [eis, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨h, w, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨g * h, w, ?_⟩
    rw [map_mul, Module.End.mul_apply]
  exact hle (Submodule.mem_map_of_mem hv)

def cuspSub : Subrepresentation ρ :=
  ⟨cusp ρ, fun g _ hv => cusp_stable ρ g hv⟩

def eisSub : Subrepresentation ρ :=
  ⟨eis ρ, fun g _ hv => eis_stable ρ g hv⟩

theorem uniSum_mem_sub (σ : Subrepresentation ρ) {v : V} (hv : v ∈ σ.toSubmodule) :
    uniSum ρ v ∈ σ.toSubmodule := by
  rw [uniSum_apply]
  exact Submodule.sum_mem _ (fun t _ => σ.apply_mem_toSubmodule _ hv)

theorem isCompl_toSubmodule {σ τ : Subrepresentation ρ} (h : IsCompl σ τ) :
    IsCompl σ.toSubmodule τ.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    have h1 := h.disjoint
    rw [disjoint_iff] at h1
    exact congrArg Subrepresentation.toSubmodule h1
  · rw [codisjoint_iff]
    have h1 := h.codisjoint
    rw [codisjoint_iff] at h1
    exact congrArg Subrepresentation.toSubmodule h1

scoped instance instFiniteGL2 : Finite (GL2 q) := by
  unfold GL2 Matrix.GeneralLinearGroup
  infer_instance

theorem neZero_card [CharZero K] : NeZero (Nat.card (GL2 q) : K) := by
  refine ⟨?_⟩
  have h : 0 < Nat.card (GL2 q) := Nat.card_pos
  exact_mod_cast h.ne'

theorem cusp_inf_eis_eq_bot [CharZero K] : cusp ρ ⊓ eis ρ = ⊥ := by
  haveI := neZero_card (q := q) (K := K)
  have hqne : (q : K) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  obtain ⟨U'', hU''⟩ := ComplementedLattice.exists_isCompl (cuspSub ρ ⊓ eisSub ρ)
  have hc : IsCompl (cusp ρ ⊓ eis ρ) U''.toSubmodule := isCompl_toSubmodule ρ hU''
  have h1 : ∀ w : V, uniSum ρ w ∈ U''.toSubmodule := by
    intro w
    have hmem : uniSum ρ w ∈ (cusp ρ ⊓ eis ρ) ⊔ U''.toSubmodule := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    have hNa : uniSum ρ a = 0 := by
      have := (Submodule.mem_inf.mp ha).1 1
      simpa using this
    have hq : (q : K) • uniSum ρ w = uniSum ρ b := by
      rw [← uniSum_uniSum, ← hab, map_add, hNa, zero_add]
    have hw : uniSum ρ w = (q : K)⁻¹ • uniSum ρ b := by
      rw [← hq, smul_smul, inv_mul_cancel₀ hqne, one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ (uniSum_mem_sub ρ U'' hb)
  have h2 : eis ρ ≤ U''.toSubmodule := by
    rw [eis]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, w, rfl⟩
    exact U''.apply_mem_toSubmodule g (h1 w)
  have h3 := hc.disjoint
  rw [disjoint_iff] at h3
  refine le_bot_iff.mp ?_
  calc cusp ρ ⊓ eis ρ = (cusp ρ ⊓ eis ρ) ⊓ eis ρ := by rw [inf_assoc, inf_idem]
    _ ≤ (cusp ρ ⊓ eis ρ) ⊓ U''.toSubmodule := inf_le_inf_left _ h2
    _ = ⊥ := h3

theorem span_fixed_le_eis [CharZero K] :
    Submodule.span K {x : V | ∃ (g : GL2 q) (v : V),
      (∀ t : ZMod q, ρ (unipotent q t) v = v) ∧ ρ g v = x} ≤ eis ρ := by
  have hqne : (q : K) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  apply Submodule.span_le.mpr
  rintro _ ⟨g, v, hv, rfl⟩
  have h1 : v = (q : K)⁻¹ • uniSum ρ v := by
    rw [uniSum_of_fixed ρ hv, smul_smul, inv_mul_cancel₀ hqne, one_smul]
  rw [h1, map_smul]
  exact Submodule.smul_mem _ _ (rho_uniSum_mem_eis ρ g v)

theorem comm_uniSum (T : V →ₗ[K] V) (hT : ∀ g : GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) (v : V) :
    T (uniSum ρ v) = uniSum ρ (T v) := by
  rw [uniSum_apply, uniSum_apply, map_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact LinearMap.congr_fun (hT (unipotent q t)) v

theorem comm_cusp (T : V →ₗ[K] V) (hT : ∀ g : GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) {v : V} (hv : v ∈ cusp ρ) :
    T v ∈ cusp ρ := by
  intro g
  have h1 : ρ g (T v) = T (ρ g v) := (LinearMap.congr_fun (hT g) v).symm
  rw [h1, ← comm_uniSum ρ T hT, hv g, map_zero]

theorem apply_eq_self_of_mem_cusp [CharZero K] (T : V →ₗ[K] V)
    (hT : ∀ g : GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T)
    (hTE : ∀ w : V, T w - w ∈ Submodule.span K {x : V | ∃ (g : GL2 q) (v : V),
      (∀ t : ZMod q, ρ (unipotent q t) v = v) ∧ ρ g v = x})
    {v : V} (hv : v ∈ cusp ρ) : T v = v := by
  have h1 : T v - v ∈ cusp ρ := Submodule.sub_mem _ (comm_cusp ρ T hT hv) hv
  have h2 : T v - v ∈ eis ρ := span_fixed_le_eis ρ (hTE v)
  have h3 : T v - v ∈ cusp ρ ⊓ eis ρ := Submodule.mem_inf.mpr ⟨h1, h2⟩
  rw [cusp_inf_eis_eq_bot ρ, Submodule.mem_bot] at h3
  exact sub_eq_zero.mp h3

end FiniteGroup

section Residue

theorem isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L] (P : ValuationSubring L) :
    IsAlgClosed (ResidueField P) := by
  refine IsAlgClosed.of_exists_root _ (fun g hg hirr => ?_)
  have hlift : g ∈ Polynomial.lifts (IsLocalRing.residue P) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective g
  obtain ⟨f, hfg, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hg
  have hinj : Function.Injective (algebraMap P L) := FaithfulSMul.algebraMap_injective P L
  have hdeg0 : (f.map (algebraMap P L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg0
  have hint : IsIntegral P r := by
    refine ⟨f, hmon, ?_⟩
    rw [← Polynomial.eval_map]
    exact hr
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := L)).mp hint
  refine ⟨IsLocalRing.residue P y, ?_⟩
  have hfy : f.eval y = 0 := by
    apply hinj
    have h1 : (f.map (algebraMap P L)).eval r = 0 := hr
    rw [← hy, Polynomial.eval_map, Polynomial.eval₂_hom] at h1
    rw [h1, map_zero]
  rw [← hfg, Polynomial.eval_map, Polynomial.eval₂_hom, hfy, map_zero]

theorem charP_residueField (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) : CharP (ResidueField P) q := by
  have h1 : ((q : P) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by simp
  have hmem : (q : P) ∈ maximalIdeal P := by
    rw [← ValuationSubring.coe_mem_nonunits_iff, h1]
    exact hP
  have h0 : (q : ResidueField P) = 0 := by
    rw [← map_natCast (IsLocalRing.residue P), IsLocalRing.residue_eq_zero_iff]
    exact hmem
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

theorem exists_ringHom_galoisField (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) : Nonempty (GaloisField q 2 →+* ResidueField P) := by
  haveI := charP_residueField q P hP
  haveI := isAlgClosed_residueField P
  letI : Algebra (ZMod q) (ResidueField P) := ZMod.algebra _ q
  exact ⟨(IsAlgClosed.lift : GaloisField q 2 →ₐ[ZMod q] ResidueField P).toRingHom⟩

theorem smul_idx_eq_self (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (hτ1 : P.tameCharacter π τ = 1) (ζ : ModularCurve.FullLevel.Idx q) : τ • ζ = ζ := by
  obtain ⟨ι⟩ := exists_ringHom_galoisField q P hP
  have h := ModularCurve.FullLevel.Idx.smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ q P hP π hπ ι hτ
    1 (by rw [Units.val_one, map_one, hτ1]) 1 (by simp) ζ
  rw [h]
  apply ModularCurve.FullLevel.Idx.ext
  haveI : Fact (1 < q) := ⟨(Fact.out : q.Prime).one_lt⟩
  rw [ModularCurve.FullLevel.Idx.val_pow, Units.val_one, ZMod.val_one, pow_one]

end Residue

section Main

open ModularCurve ModularCurve.FullLevel CuspidalType

noncomputable def rhoV (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] :
    Representation ℚ_[lam] (GL2 q) (RationalTateModule lam (Jac q M')) :=
  (Module.End.baseChangeHom ℤ_[lam] ℚ_[lam] (TateModule lam (Jac q M')) :
      Module.End ℤ_[lam] (TateModule lam (Jac q M')) →* Module.End ℚ_[lam] (RationalTateModule lam (Jac q M'))).comp
    (tateGL2 q M' lam)

theorem rhoV_apply (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (g : GL2 q) :
    rhoV q M' lam g = (tateGL2 q M' lam g).baseChange ℚ_[lam] :=
  rfl

set_option maxHeartbeats 1600000 in

theorem fix_of_cusp
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime]
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hspanτ : LinearMap.range ((tateGal q M' lam τ).baseChange ℚ_[lam] - 1) ≤
          Submodule.span ℚ_[lam] {x : RationalTateModule lam (Jac q M') |
            ∃ (g : GL2 q) (v : RationalTateModule lam (Jac q M')),
              (∀ t : ZMod q, (tateGL2 q M' lam (unipotent q t)).baseChange ℚ_[lam] v = v) ∧
              (tateGL2 q M' lam g).baseChange ℚ_[lam] v = x})
    (v : RationalTateModule lam (Jac q M'))
    (hv : ∀ g : GL2 q,
      (∑ t : ZMod q, (tateGL2 q M' lam (unipotent q t)).baseChange ℚ_[lam] *
          (tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) :
    (tateGal q M' lam τ).baseChange ℚ_[lam] v = v := by
  have hvC : v ∈ cusp (rhoV q M' lam) := by
    intro g
    rw [← sum_mul_apply]
    exact hv g
  have hcomm : ∀ g : GL2 q,
      (tateGal q M' lam τ).baseChange ℚ_[lam] ∘ₗ rhoV q M' lam g =
        rhoV q M' lam g ∘ₗ (tateGal q M' lam τ).baseChange ℚ_[lam] := by
    intro g
    rw [rhoV_apply, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    have h := ModularCurve.FullLevel.tateGal_mul_tateGL2_comm q M' hqM' lam τ g
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp] at h
    rw [h]
  refine apply_eq_self_of_mem_cusp (rhoV q M' lam) _ hcomm ?_ hvC
  intro w
  have hw : (tateGal q M' lam τ).baseChange ℚ_[lam] w - w =
      ((tateGal q M' lam τ).baseChange ℚ_[lam] - 1) w := by
    rw [LinearMap.sub_apply, Module.End.one_apply]
  rw [hw]
  exact hspanτ (LinearMap.mem_range_self _ w)

set_option maxHeartbeats 3200000 in

theorem coord_formula
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (hΨ₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule lam (Jac q M')) (ζ : Idx q),
        Ψ (tateGal q M' lam σ x) ζ = JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam σ (Ψ x (σ⁻¹ • ζ)))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : Idx q) (w : RationalTateModule lam (Jac q M')) :
    ratCoord q M' lam Ψ ζ ((tateGal q M' lam τ).baseChange ℚ_[lam] w) =
      (JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam τ).baseChange ℚ_[lam]
        (ratCoord q M' lam Ψ (τ⁻¹ • ζ) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    have h1 : ratCoord q M' lam Ψ (τ⁻¹ • ζ) (a ⊗ₜ x) = a ⊗ₜ Ψ x (τ⁻¹ • ζ) := rfl
    have h2 : ∀ (y : TateModule lam (jacComp q M')),
        (JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam τ).baseChange ℚ_[lam] (a ⊗ₜ y) =
          a ⊗ₜ JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam τ y := fun y => rfl
    have h3 : ratCoord q M' lam Ψ ζ ((tateGal q M' lam τ).baseChange ℚ_[lam] (a ⊗ₜ x)) =
        a ⊗ₜ Ψ (tateGal q M' lam τ x) ζ := rfl
    rw [h1, h2, h3, hΨ₂]
  | add x y hx hy =>
    rw [((tateGal q M' lam τ).baseChange ℚ_[lam]).map_add, (ratCoord q M' lam Ψ ζ).map_add, hx, hy,
      (ratCoord q M' lam Ψ (τ⁻¹ • ζ)).map_add,
      ((JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam τ).baseChange ℚ_[lam]).map_add]

theorem rationalGaloisRep_arithmeticGalois
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) =
      (JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam τ).baseChange ℚ_[lam] := by
  have hR0 : TateModule.rep lam (Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
        (arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) =
      JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam τ := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    rfl
  rw [rationalGaloisRep_apply, hR0]

set_option maxHeartbeats 3200000 in
theorem main
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (hspan : ∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
        LinearMap.range ((ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] - 1) ≤
          Submodule.span ℚ_[lam] {x : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') |
            ∃ (g : CuspidalType.GL2 q) (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')),
              (∀ t : ZMod q,
                (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] v = v) ∧
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam] v = x})
    (Ψ : TateModule lam (ModularCurve.FullLevel.Jac q M') ≃ₗ[ℤ_[lam]]
        (ModularCurve.FullLevel.Idx q → TateModule lam (ModularCurve.FullLevel.jacComp q M')))
    (hΨ₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M'))
          (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateGal q M' lam σ x) ζ =
          ModularCurve.JH.tateGaloisRep (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam σ (Ψ x (σ⁻¹ • ζ)))
    (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'))
    (hv : ∀ g : CuspidalType.GL2 q,
      (∑ t : ZMod q,
        (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
          (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0)
    (ζ : ModularCurve.FullLevel.Idx q) :
    ModularCurve.FullLevel.ratCoord q M' lam Ψ ζ v ∈
      ⨅ s ∈ {s : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
            s = ModularCurve.arithmeticGalois
              (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ},
        LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1) := by
  rw [Submodule.mem_iInf]
  intro s
  rw [Submodule.mem_iInf]
  rintro ⟨τ, hτI, hτ1, rfl⟩

  have hfix : (tateGal q M' lam τ).baseChange ℚ_[lam] v = v :=
    fix_of_cusp q M' hqM' lam τ (hspan τ hτI hτ1) v hv

  have hζ : τ • ζ = ζ := smul_idx_eq_self q P hP π hπ hτI hτ1 ζ
  have hζ' : τ⁻¹ • ζ = ζ := by
    rw [inv_smul_eq_iff, hζ]

  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    rationalGaloisRep_arithmeticGalois]
  have h := coord_formula q M' lam Ψ hΨ₂ τ ζ v
  rw [hfix, hζ'] at h
  exact h.symm

end Main

end InvHspanSol
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero.InvHspanSol"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)

    (hspan : ∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
        LinearMap.range ((ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] - 1) ≤
          Submodule.span ℚ_[lam] {x : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') |
            ∃ (g : CuspidalType.GL2 q) (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')),
              (∀ t : ZMod q,
                (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] v = v) ∧
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam] v = x})

    (Ψ : TateModule lam (ModularCurve.FullLevel.Jac q M') ≃ₗ[ℤ_[lam]]
        (ModularCurve.FullLevel.Idx q → TateModule lam (ModularCurve.FullLevel.jacComp q M')))
    (hΨ₁ : ∀ (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (ζ : ModularCurve.FullLevel.Idx q) (n : ℕ),
        ((Ψ x ζ : TateModule lam (ModularCurve.FullLevel.jacComp q M')) : ℕ → ModularCurve.FullLevel.jacComp q M') n =
          (((x : TateModule lam (ModularCurve.FullLevel.Jac q M')) : ℕ → ModularCurve.FullLevel.Jac q M') n).eval ζ)
    (hΨ₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M'))
          (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateGal q M' lam σ x) ζ =
          ModularCurve.JH.tateGaloisRep (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam σ (Ψ x (σ⁻¹ • ζ)))
    (hΨ₃ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M'))
          (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.slJac q M' γ) x) ζ =
          ModularCurve.JH.tateEnd (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam
            (ModularCurve.FullLevel.levelOp q M' ζ γ⁻¹) (Ψ x ζ))
    (hΨ₄ : ∀ (d : (ZMod q)ˣ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.diagJac q M' d) x) ζ = Ψ x (ζ.pow d⁻¹))
    (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'))
    (hv : ∀ g : CuspidalType.GL2 q,
      (∑ t : ZMod q,
        (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
          (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0)
    (ζ : ModularCurve.FullLevel.Idx q) :
    ModularCurve.FullLevel.ratCoord q M' lam Ψ ζ v ∈
      ⨅ s ∈ {s : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
            s = ModularCurve.arithmeticGalois
              (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ},
        LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1) :=
  InvHspanSol.main q M' hqM' lam P hP π hπ hspan Ψ hΨ₂ v hv ζ

end S_ModularCurve_FullLevel_ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero
end P2MW
export P2MW.S_ModularCurve_FullLevel_ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero (solution)
