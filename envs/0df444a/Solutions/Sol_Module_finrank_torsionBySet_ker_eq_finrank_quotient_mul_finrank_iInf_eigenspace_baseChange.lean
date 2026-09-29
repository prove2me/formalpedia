-- Prove2me | solution 1 for Module.finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3c971e43-7348-5075-85ec-d159ca41db94

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKAlg2Sol

open Module Polynomial
open scoped Matrix TensorProduct

section Integral

theorem exists_algebraMap_eq_mul {𝒪 Q : Type*} [CommRing 𝒪] [CommRing Q] [IsDomain Q]
    [Algebra 𝒪 Q] {q : Q} (hint : IsIntegral 𝒪 q) (hq : q ≠ 0) :
    ∃ (c : 𝒪) (s : Q), c ≠ 0 ∧ algebraMap 𝒪 Q c = s * q := by
  haveI : Nontrivial 𝒪 := (algebraMap 𝒪 Q).domain_nontrivial
  obtain ⟨p, hpm, hp⟩ := hint
  have hp0 : p ≠ 0 := hpm.ne_zero
  obtain ⟨r, hr, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hr0 : r.coeff 0 ≠ 0 := by
    intro h
    apply hndvd
    rw [map_zero, sub_zero]
    exact Polynomial.X_dvd_iff.mpr h
  have haev : Polynomial.aeval q r = 0 := by
    have h1 : Polynomial.aeval q p = 0 := hp
    rw [hr, map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_zero,
      sub_zero] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (pow_ne_zero _ hq)
    · exact h
  refine ⟨r.coeff 0, -(Polynomial.aeval q r.divX), hr0, ?_⟩
  have h2 := congrArg (Polynomial.aeval q) (Polynomial.divX_mul_X_add r)
  rw [haev, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  linear_combination h2

theorem exists_smul_mem_of_smul_mem {𝒪 Q V : Type*} [CommRing 𝒪] [CommRing Q] [IsDomain Q]
    [Algebra 𝒪 Q] [Algebra.IsIntegral 𝒪 Q] [AddCommGroup V] [Module Q V] [Module 𝒪 V]
    [IsScalarTower 𝒪 Q V] (F : Submodule Q V) {q : Q} (hq : q ≠ 0) {v : V} (hv : q • v ∈ F) :
    ∃ c : 𝒪, c ≠ 0 ∧ c • v ∈ F := by
  obtain ⟨c, s, hc, hcs⟩ := exists_algebraMap_eq_mul (Algebra.IsIntegral.isIntegral (R := 𝒪) q) hq
  refine ⟨c, hc, ?_⟩
  have : c • v = s • (q • v) := by
    rw [← algebraMap_smul Q c v, hcs, mul_smul]
  rw [this]
  exact F.smul_mem s hv

theorem exists_forall_smul_eq_zero {𝒪 W : Type*} [CommRing 𝒪] [IsDomain 𝒪] [AddCommGroup W]
    [Module 𝒪 W] [Module.Finite 𝒪 W] (h : ∀ w : W, ∃ c : 𝒪, c ≠ 0 ∧ c • w = 0) :
    ∃ c : 𝒪, c ≠ 0 ∧ ∀ w : W, c • w = 0 := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := 𝒪) (M := W)
  choose c hc hcs using fun j => h (s j)
  refine ⟨∏ j, c j, Finset.prod_ne_zero_iff.mpr fun j _ => hc j, fun w => ?_⟩
  have hw : w ∈ Submodule.span 𝒪 (Set.range s) := by rw [hs]; exact Submodule.mem_top
  obtain ⟨g, rfl⟩ := Submodule.mem_span_range_iff_exists_fun 𝒪 |>.mp hw
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_comm, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ j), mul_comm, mul_smul,
    hcs j, smul_zero, smul_zero]

theorem exists_forall_smul_mem {𝒪 Q V : Type*} [CommRing 𝒪] [IsDomain 𝒪] [CommRing Q]
    [Algebra 𝒪 Q] [AddCommGroup V] [Module Q V] [Module 𝒪 V] [IsScalarTower 𝒪 Q V]
    [Module.Finite 𝒪 V] (F : Submodule Q V) (h : ∀ v : V, ∃ c : 𝒪, c ≠ 0 ∧ c • v ∈ F) :
    ∃ c : 𝒪, c ≠ 0 ∧ ∀ v : V, c • v ∈ F := by
  haveI : Module.Finite 𝒪 (V ⧸ F) :=
    Module.Finite.of_surjective (F.mkQ.restrictScalars 𝒪) (Submodule.mkQ_surjective F)
  have h' : ∀ w : V ⧸ F, ∃ c : 𝒪, c ≠ 0 ∧ c • w = 0 := by
    intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective F w
    obtain ⟨c, hc, hcv⟩ := h v
    refine ⟨c, hc, ?_⟩
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hcv
  obtain ⟨c, hc, hcw⟩ := exists_forall_smul_eq_zero h'
  refine ⟨c, hc, fun v => ?_⟩
  have := hcw (Submodule.Quotient.mk v)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

end Integral

section Tower

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
variable {Q : Type*} [CommRing Q] [IsDomain Q] [Algebra 𝒪 Q] [Module.Finite 𝒪 Q]
  [IsTorsionFree 𝒪 Q]
variable {V : Type*} [AddCommGroup V] [Module Q V] [Module 𝒪 V] [IsScalarTower 𝒪 Q V]
  [Module.Finite 𝒪 V] [IsTorsionFree 𝒪 V]

theorem finrank_span_of_linearIndependent {n : ℕ} {b : Fin n → V} (hb : LinearIndependent Q b) :
    finrank 𝒪 ↥(Submodule.span Q (Set.range b)) = n * finrank 𝒪 Q := by
  haveI : Module.Free 𝒪 Q := Module.free_of_finite_type_torsion_free'
  have e : (Fin n → Q) ≃ₗ[𝒪] ↥(Submodule.span Q (Set.range b)) :=
    ((Finsupp.linearEquivFunOnFinite Q Q (Fin n)).symm.trans hb.linearCombinationEquiv).restrictScalars 𝒪
  rw [← e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

theorem exists_forall_smul_mem_of_isTorsion (F : Submodule Q V)
    (hF : Module.IsTorsion Q (V ⧸ F)) : ∃ c : 𝒪, c ≠ 0 ∧ ∀ v : V, c • v ∈ F := by
  haveI : Algebra.IsIntegral 𝒪 Q := Algebra.IsIntegral.of_finite 𝒪 Q
  refine exists_forall_smul_mem F fun v => ?_
  obtain ⟨⟨q, hq⟩, hqv⟩ := @hF (Submodule.Quotient.mk v)
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hmem : q • v ∈ F := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hqv
  exact exists_smul_mem_of_smul_mem F hq0 hmem

theorem isTorsion_quotient_of_finrank_eq [Module.Finite Q V] (F : Submodule Q V)
    (hF : finrank Q ↥F = finrank Q V) : Module.IsTorsion Q (V ⧸ F) := by
  rw [← Module.finrank_eq_zero_iff_isTorsion]
  have := Submodule.finrank_quotient_add_finrank F
  omega

omit [IsTorsionFree 𝒪 V] in

theorem finrank_eq_zero_of_forall_smul_eq_zero {W : Type*} [AddCommGroup W] [Module 𝒪 W]
    [Module.Finite 𝒪 W] {c : 𝒪} (hc : c ≠ 0) (h : ∀ w : W, c • w = 0) : finrank 𝒪 W = 0 := by
  rw [Module.finrank_eq_zero_iff_isTorsion]
  intro w
  exact ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, h w⟩

theorem finrank_eq_finrank_mul_finrank [IsTorsionFree Q V] :
    finrank 𝒪 V = finrank Q V * finrank 𝒪 Q := by
  haveI : Module.Finite Q V := Module.Finite.of_restrictScalars_finite 𝒪 Q V
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := Q) (M := V) (le_refl (finrank Q V))
  set F : Submodule Q V := Submodule.span Q (Set.range b) with hFdef
  have hFrank : finrank Q ↥F = finrank Q V := finrank_span_eq_card hb |>.trans (Fintype.card_fin _)
  obtain ⟨c, hc, hcF⟩ := exists_forall_smul_mem_of_isTorsion (𝒪 := 𝒪) F
    (isTorsion_quotient_of_finrank_eq F hFrank)

  haveI : Module.Finite 𝒪 (V ⧸ F) :=
    Module.Finite.of_surjective (F.mkQ.restrictScalars 𝒪) (Submodule.mkQ_surjective F)
  have hq0 : finrank 𝒪 (V ⧸ F) = 0 := by
    refine finrank_eq_zero_of_forall_smul_eq_zero hc fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective F w
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hcF v
  have h1 : finrank 𝒪 (V ⧸ F) = finrank 𝒪 V - finrank 𝒪 ↥F := Submodule.finrank_quotient F
  have h2 : finrank 𝒪 ↥F ≤ finrank 𝒪 V :=
    LinearMap.finrank_le_finrank_of_injective (f := F.subtype.restrictScalars 𝒪)
      Subtype.val_injective
  have h3 : finrank 𝒪 ↥F = finrank Q V * finrank 𝒪 Q := finrank_span_of_linearIndependent hb
  omega

theorem exists_linearIndependent_and_smul_mem_span [IsTorsionFree Q V] (d : ℕ)
    (h : finrank 𝒪 V = d * finrank 𝒪 Q) :
    ∃ (b : Fin d → V) (c : 𝒪), LinearIndependent Q b ∧ c ≠ 0 ∧
      ∀ v : V, ∃ g : Fin d → Q, c • v = ∑ k, g k • b k := by
  haveI : Module.Finite Q V := Module.Finite.of_restrictScalars_finite 𝒪 Q V
  have hpos : 0 < finrank 𝒪 Q := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩
  have hd : finrank Q V = d := by
    have := finrank_eq_finrank_mul_finrank (𝒪 := 𝒪) (Q := Q) (V := V)
    rw [h] at this
    exact (Nat.eq_of_mul_eq_mul_right hpos this).symm
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := Q) (M := V) (n := d) hd.ge
  set F : Submodule Q V := Submodule.span Q (Set.range b) with hFdef
  have hFrank : finrank Q ↥F = finrank Q V :=
    (finrank_span_eq_card hb).trans ((Fintype.card_fin _).trans hd.symm)
  obtain ⟨c, hc, hcF⟩ := exists_forall_smul_mem_of_isTorsion (𝒪 := 𝒪) F
    (isTorsion_quotient_of_finrank_eq F hFrank)
  refine ⟨b, c, hb, hc, fun v => ?_⟩
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun Q).mp (hcF v)
  exact ⟨g, hg.symm⟩

end Tower

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
variable {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
variable {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  [Module.Finite 𝒪 M] [IsTorsionFree 𝒪 M]

theorem isTorsionFree_of_injective {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [IsTorsionFree R Y] (g : X →ₗ[R] Y)
    (hg : Function.Injective g) : IsTorsionFree R X :=
  Function.Injective.moduleIsTorsionFree g hg (map_smul g)

theorem isTorsionFree_quotient_ker {A : Type*} [CommRing A] [Algebra 𝒪 A] [IsTorsionFree 𝒪 A]
    (χ : T →ₐ[𝒪] A) : IsTorsionFree 𝒪 (T ⧸ RingHom.ker χ) := by
  let g : (T ⧸ RingHom.ker χ) →ₐ[𝒪] A := Ideal.kerLiftAlg χ
  have hg : Function.Injective g := Ideal.kerLiftAlg_injective χ
  exact Function.Injective.moduleIsTorsionFree g hg (map_smul g)

theorem isTorsionFree_torsionBySet_quotient {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A]
    [IsTorsionFree 𝒪 A] (χ : T →ₐ[𝒪] A) :
    haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
    IsTorsionFree (T ⧸ RingHom.ker χ) ↥(Submodule.torsionBySet T M ↑(RingHom.ker χ)) := by
  haveI hprime : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime _
  haveI : IsDomain (T ⧸ RingHom.ker χ) := Ideal.Quotient.isDomain _
  haveI : Module.Finite 𝒪 (T ⧸ RingHom.ker χ) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 (RingHom.ker χ)).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral 𝒪 (T ⧸ RingHom.ker χ) := Algebra.IsIntegral.of_finite 𝒪 _
  set V := Submodule.torsionBySet T M ↑(RingHom.ker χ) with hVdef
  haveI : IsTorsionFree 𝒪 ↥V := isTorsionFree_of_injective (V.subtype.restrictScalars 𝒪)
    Subtype.val_injective
  refine ⟨fun q hq => ?_⟩

  have hq0 : q ≠ 0 := hq.ne_zero
  obtain ⟨c, s, hc, hcs⟩ := exists_algebraMap_eq_mul (Algebra.IsIntegral.isIntegral (R := 𝒪) q) hq0
  intro v w hvw
  have h1 : c • v = c • w := by
    have : ∀ u : ↥V, c • u = s • (q • u) := fun u => by
      rw [← algebraMap_smul (T ⧸ RingHom.ker χ) c u, hcs, mul_smul]
    rw [this, this]
    exact congrArg (s • ·) hvw
  exact (smul_right_injective (↥V) hc) h1

theorem finrank_eq_of_injective_of_smul_mem_range {X Y : Type*} [AddCommGroup X] [Module 𝒪 X]
    [AddCommGroup Y] [Module 𝒪 Y] [Module.Finite 𝒪 X] [Module.Finite 𝒪 Y] [IsTorsionFree 𝒪 Y]
    (g : X →ₗ[𝒪] Y) (hg : Function.Injective g) (c : 𝒪) (hc : c ≠ 0)
    (hcY : ∀ y, c • y ∈ LinearMap.range g) : finrank 𝒪 X = finrank 𝒪 Y := by
  apply le_antisymm (LinearMap.finrank_le_finrank_of_injective hg)
  let h : Y →ₗ[𝒪] LinearMap.range g :=
    { toFun := fun y => ⟨c • y, hcY y⟩
      map_add' := fun y y' => Subtype.ext (smul_add c y y')
      map_smul' := fun r y => Subtype.ext (smul_comm c r y) }
  have hh : Function.Injective h := by
    intro y y' hyy'
    have : c • y = c • y' := congrArg Subtype.val hyy'
    exact (smul_right_injective Y hc) this
  calc finrank 𝒪 Y ≤ finrank 𝒪 (LinearMap.range g) := LinearMap.finrank_le_finrank_of_injective hh
    _ = finrank 𝒪 X := LinearMap.finrank_range_of_inj hg

end Main

section Crux

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
  [IsTorsionFree 𝒪 R]
variable {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
  [IsTorsionFree 𝒪 A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def eigenLattice {τ : Type*} (φ : τ → R) (ρ : τ → Matrix ι ι 𝒪) : Submodule 𝒪 (ι → R) where
  carrier := {w | ∀ t i, φ t * w i = ∑ j, ρ t i j • w j}
  add_mem' {v w} hv hw t i := by
    simp only [Pi.add_apply, mul_add, smul_add, Finset.sum_add_distrib, hv t i, hw t i]
  zero_mem' t i := by simp
  smul_mem' c w hw t i := by
    simp only [Pi.smul_apply, mul_smul_comm, hw t i, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]

omit [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [IsDomain R] [Module.Finite 𝒪 R] [IsTorsionFree 𝒪 R]
  [DecidableEq ι] in
theorem mem_eigenLattice {τ : Type*} (φ : τ → R) (ρ : τ → Matrix ι ι 𝒪) (w : ι → R) :
    w ∈ eigenLattice φ ρ ↔ ∀ t i, φ t * w i = ∑ j, ρ t i j • w j := Iff.rfl

omit [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [IsDomain R] [Module.Finite 𝒪 R] [IsTorsionFree 𝒪 R]
  [DecidableEq ι] in

theorem mulVec_mem_eigenLattice_transpose {τ : Type*} (φ : τ → R) (ρ : τ → Matrix ι ι 𝒪)
    (G : Matrix ι ι 𝒪) (hG : ∀ t, G * ρ t = (ρ t)ᵀ * G) {w : ι → R} (hw : w ∈ eigenLattice φ ρ) :
    (fun i => ∑ j, G i j • w j) ∈ eigenLattice φ (fun t => (ρ t)ᵀ) := by
  intro t i
  simp only [Matrix.transpose_apply, Finset.mul_sum, mul_smul_comm, Finset.smul_sum]

  calc ∑ j, G i j • (φ t * w j) = ∑ j, G i j • ∑ k, ρ t j k • w k := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [hw t j]
    _ = ∑ k, ∑ j, (G i j * ρ t j k) • w k := by
        simp only [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]
    _ = ∑ k, ∑ j, (ρ t j i * G j k) • w k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have := congrArg (fun P : Matrix ι ι 𝒪 => P i k) (hG t)
        simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
        rw [← Finset.sum_smul, ← Finset.sum_smul, this]
    _ = ∑ x, ∑ x_1, ρ t x i • G x x_1 • w x_1 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul]

theorem finrank_eigenLattice_le {τ : Type*} (φ : τ → R) (ρ : τ → Matrix ι ι 𝒪)
    (G : Matrix ι ι 𝒪) (hG : ∀ t, G * ρ t = (ρ t)ᵀ * G) (hdet : G.det ≠ 0) :
    finrank 𝒪 ↥(eigenLattice φ ρ) ≤ finrank 𝒪 ↥(eigenLattice φ fun t => (ρ t)ᵀ) := by
  haveI : IsNoetherian 𝒪 (ι → R) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
  haveI : Module.Finite 𝒪 ↥(eigenLattice φ fun t => (ρ t)ᵀ) :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  let g : ↥(eigenLattice φ ρ) →ₗ[𝒪] ↥(eigenLattice φ fun t => (ρ t)ᵀ) :=
    { toFun := fun w => ⟨fun i => ∑ j, G i j • (w : ι → R) j,
        mulVec_mem_eigenLattice_transpose φ ρ G hG w.2⟩
      map_add' := fun v w => by
        ext i
        simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by
        ext i
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm] }
  refine LinearMap.finrank_le_finrank_of_injective (f := g) ?_

  intro v w hvw
  apply Subtype.ext
  have h : ∀ i, ∑ j, G i j • ((v : ι → R) j - (w : ι → R) j) = 0 := by
    intro i
    have := congrArg (fun u : ↥(eigenLattice φ fun t => (ρ t)ᵀ) => (u : ι → R) i) hvw
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk] at this
    simp only [smul_sub, Finset.sum_sub_distrib, this, sub_self]
  funext k
  rw [← sub_eq_zero]
  have hk : G.det • ((v : ι → R) k - (w : ι → R) k) = 0 := by
    have hadj : ∀ k j, ∑ i, G.adjugate k i * G i j = if k = j then G.det else 0 := by
      intro k j
      have := congrArg (fun P : Matrix ι ι 𝒪 => P k j) (Matrix.adjugate_mul G)
      simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this
    calc G.det • ((v : ι → R) k - (w : ι → R) k)
        = ∑ j, (if k = j then G.det else 0) • ((v : ι → R) j - (w : ι → R) j) := by
          rw [Finset.sum_eq_single k (fun j _ hjk => by rw [if_neg (Ne.symm hjk), zero_smul])
            (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
      _ = ∑ j, (∑ i, G.adjugate k i * G i j) • ((v : ι → R) j - (w : ι → R) j) := by
          refine Finset.sum_congr rfl fun j _ => ?_; rw [hadj]
      _ = ∑ i, G.adjugate k i • ∑ j, G i j • ((v : ι → R) j - (w : ι → R) j) := by
          simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
      _ = 0 := by simp only [h, smul_zero, Finset.sum_const_zero]
  exact (smul_eq_zero_iff_right hdet).mp hk

theorem finrank_eigenLattice_transpose_eq (φ : R →ₐ[𝒪] A) (hφ : Function.Injective φ)
    (β : Module.Basis ι 𝒪 A) :
    finrank 𝒪 ↥(eigenLattice (fun t : R => t) fun t => (Algebra.leftMulMatrix β (φ t))ᵀ) =
      finrank 𝒪 A := by
  classical

  letI : Algebra R A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪 R A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI : IsTorsionFree R A := by
    refine ⟨fun q hq x y hxy => ?_⟩
    have hq' : φ q ≠ 0 := (map_ne_zero_iff _ hφ).mpr hq.ne_zero
    have : φ q * x = φ q * y := by simp only [Algebra.smul_def] at hxy; exact hxy
    exact mul_left_cancel₀ hq' this
  haveI : IsNoetherian 𝒪 (ι → R) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
  set E := eigenLattice (fun t : R => t) fun t => (Algebra.leftMulMatrix β (φ t))ᵀ with hEdef
  haveI : Module.Finite 𝒪 ↥E := Module.Finite.of_injective E.subtype Subtype.val_injective
  haveI : IsTorsionFree 𝒪 ↥E := isTorsionFree_of_injective E.subtype Subtype.val_injective

  set s := finrank R A with hsdef
  obtain ⟨α, c, hα, hc, hcα⟩ := exists_linearIndependent_and_smul_mem_span (𝒪 := 𝒪) (Q := R)
    (V := A) s (finrank_eq_finrank_mul_finrank (𝒪 := 𝒪) (Q := R) (V := A))

  let lam : (ι → R) → (A →ₗ[𝒪] R) := fun w => β.constr 𝒪 w
  have hlam_β : ∀ w i, lam w (β i) = w i := fun w i => β.constr_basis 𝒪 w i
  have hlam_mul : ∀ w, w ∈ E ↔ ∀ (t : R) (y : A), lam w (φ t * y) = t * lam w y := by
    intro w
    constructor
    · intro hw t

      suffices h : (lam w).comp (LinearMap.mulLeft 𝒪 (φ t)) = t • lam w by
        intro y
        have := LinearMap.congr_fun h y
        simpa [LinearMap.mulLeft_apply, smul_eq_mul] using this
      refine β.ext fun i => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hlam_β, (mem_eigenLattice _ _ _).mp hw t i]
      conv_lhs => rw [← β.sum_repr (φ t * β i)]
      simp only [map_sum, map_smul, hlam_β, Matrix.transpose_apply,
        Algebra.leftMulMatrix_eq_repr_mul]
    · intro h t i
      have := h t (β i)
      rw [hlam_β] at this
      rw [← this]
      conv_lhs => rw [← β.sum_repr (φ t * β i)]
      simp only [map_sum, map_smul, hlam_β, Matrix.transpose_apply,
        Algebra.leftMulMatrix_eq_repr_mul]

  let Ψ : ↥E →ₗ[𝒪] (Fin s → R) :=
    { toFun := fun w k => lam (w : ι → R) (α k)
      map_add' := fun v w => by
        funext k; simp only [lam, Submodule.coe_add, map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun r w => by
        funext k
        simp only [lam, Submodule.coe_smul, map_smul, LinearMap.smul_apply, Pi.smul_apply,
          RingHom.id_apply] }
  have hΨapply : ∀ (w : ↥E) k, Ψ w k = lam (w : ι → R) (α k) := fun w k => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hwE := (hlam_mul (w : ι → R)).mp w.2

    have hzero : ∀ y : A, lam (w : ι → R) y = 0 := by
      intro y
      obtain ⟨g, hg⟩ := hcα y
      have h1 : lam (w : ι → R) (c • y) = 0 := by
        rw [hg, map_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Algebra.smul_def, show algebraMap R A (g k) = φ (g k) from rfl, hwE]
        have : lam (w : ι → R) (α k) = 0 := by rw [← hΨapply, hw]; rfl
        rw [this, mul_zero]
      rw [map_smul] at h1
      exact (smul_eq_zero_iff_right hc).mp h1
    apply Subtype.ext
    funext i
    rw [← hlam_β (w : ι → R) i, hzero]
    rfl
  have hΨsurj : ∀ u : Fin s → R, c • u ∈ LinearMap.range Ψ := by
    intro u

    let Bα := Module.Basis.span hα
    let g : ↥(Submodule.span R (Set.range α)) →ₗ[R] R := Bα.constr R u
    have hg : ∀ k, g ⟨α k, Submodule.subset_span (Set.mem_range_self k)⟩ = u k := by
      intro k
      have h1 : (⟨α k, Submodule.subset_span (Set.mem_range_self k)⟩ :
          ↥(Submodule.span R (Set.range α))) = Bα k := by
        apply Subtype.ext; rw [Module.Basis.span_apply]
      rw [h1]; exact Bα.constr_basis R u k
    have hmem : ∀ y : A, c • y ∈ Submodule.span R (Set.range α) := by
      intro y
      obtain ⟨g', hg'⟩ := hcα y
      rw [hg']
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_range_self k))
    have hmk_add : ∀ y y' : A, (⟨c • (y + y'), hmem (y + y')⟩ : ↥(Submodule.span R (Set.range α))) =
        ⟨c • y, hmem y⟩ + ⟨c • y', hmem y'⟩ := fun y y' => Subtype.ext (smul_add c y y')
    have hmk_smul : ∀ (r : 𝒪) (y : A), (⟨c • (r • y), hmem (r • y)⟩ :
        ↥(Submodule.span R (Set.range α))) = r • ⟨c • y, hmem y⟩ := fun r y =>
      Subtype.ext (smul_comm c r y)
    have hmk_R : ∀ (t : R) (y : A), (⟨c • (φ t * y), hmem (φ t * y)⟩ :
        ↥(Submodule.span R (Set.range α))) = t • ⟨c • y, hmem y⟩ := by
      intro t y
      apply Subtype.ext
      show c • (φ t * y) = t • (c • y)
      rw [Algebra.smul_def t (c • y), mul_smul_comm]
      rfl
    let μ : A →ₗ[𝒪] R :=
      { toFun := fun y => g ⟨c • y, hmem y⟩
        map_add' := fun y y' => by rw [hmk_add, map_add]
        map_smul' := fun r y => by rw [hmk_smul, LinearMap.map_smul_of_tower, RingHom.id_apply] }
    have hμapply : ∀ y, μ y = g ⟨c • y, hmem y⟩ := fun y => rfl
    have hμR : ∀ (t : R) (y : A), μ (φ t * y) = t * μ y := by
      intro t y
      rw [hμapply, hμapply, hmk_R, map_smul, smul_eq_mul]

    let w : ι → R := fun i => μ (β i)
    have hlamw : lam w = μ := β.ext fun i => by rw [hlam_β]
    have hwE : w ∈ E := (hlam_mul w).mpr (by rw [hlamw]; exact hμR)
    refine ⟨⟨w, hwE⟩, ?_⟩
    funext k
    rw [hΨapply, Pi.smul_apply]
    show lam w (α k) = c • u k
    rw [hlamw, ← hg k, ← LinearMap.map_smul_of_tower g c, hμapply]
    congr 1

  haveI : Module.Free 𝒪 R := Module.free_of_finite_type_torsion_free'
  rw [finrank_eq_of_injective_of_smul_mem_range Ψ hΨinj c hc hΨsurj, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsdef]
  exact (finrank_eq_finrank_mul_finrank (𝒪 := 𝒪) (Q := R) (V := A)).symm

end Crux

section Gram

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
variable {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
  [IsTorsionFree 𝒪 A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_repr_mul_repr (β : Module.Basis ι 𝒪 A) (i₀ i : ι) (x : A) :
    ∑ j, β.repr (β i * β j) i₀ * β.repr x j = β.repr (β i * x) i₀ := by
  conv_rhs => rw [← β.sum_repr x]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_repr_repr_mul (β : Module.Basis ι 𝒪 A) (i₀ k : ι) (x : A) :
    ∑ j, β.repr x j * β.repr (β j * β k) i₀ = β.repr (x * β k) i₀ := by
  conv_rhs => rw [← β.sum_repr x]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem gram_mul_leftMulMatrix (β : Module.Basis ι 𝒪 A) (i₀ : ι) (a : A) :
    Matrix.of (fun i j => β.repr (β i * β j) i₀) * Algebra.leftMulMatrix β a =
      (Algebra.leftMulMatrix β a)ᵀ * Matrix.of (fun i j => β.repr (β i * β j) i₀) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
    Algebra.leftMulMatrix_eq_repr_mul]
  rw [sum_repr_mul_repr β i₀ i (a * β k), sum_repr_repr_mul β i₀ k (a * β i),
    show β i * (a * β k) = a * β i * β k by ring]

theorem det_gram_ne_zero (β : Module.Basis ι 𝒪 A) (i₀ : ι) :
    (Matrix.of fun i j => β.repr (β i * β j) i₀).det ≠ 0 := by
  haveI : Nontrivial 𝒪 := (algebraMap 𝒪 A).domain_nontrivial
  haveI : Algebra.IsIntegral 𝒪 A := Algebra.IsIntegral.of_finite 𝒪 A
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  set y : A := ∑ j, v j • β j with hydef
  have hyrepr : ∀ j, β.repr y j = v j := fun j => congrFun (β.repr_sum_self v) j
  have hy0 : y ≠ 0 := by
    intro h
    apply hv
    funext j
    rw [← hyrepr j, h, map_zero, Finsupp.zero_apply, Pi.zero_apply]
  have hβy : ∀ i, β.repr (β i * y) i₀ = 0 := by
    intro i
    have := congrFun hGv i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← sum_repr_mul_repr β i₀ i y]
    simpa only [hyrepr] using this
  have hxy : ∀ x : A, β.repr (x * y) i₀ = 0 := by
    intro x
    conv_lhs => rw [← β.sum_repr x]
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hβy, mul_zero,
      Finset.sum_const_zero]

  obtain ⟨c, s, hc, hcs⟩ := exists_algebraMap_eq_mul (Algebra.IsIntegral.isIntegral (R := 𝒪) y) hy0
  have h1 : β.repr (β i₀ * algebraMap 𝒪 A c) i₀ = 0 := by
    rw [hcs, ← mul_assoc, hxy]
  rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at h1
  exact hc h1

end Gram

section Final

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
variable {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
variable {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  [Module.Finite 𝒪 M] [IsTorsionFree 𝒪 M]
variable {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
  [IsTorsionFree 𝒪 A]

def eigenLatticeM {ι : Type*} [Fintype ι] (ρ : T → Matrix ι ι 𝒪) : Submodule 𝒪 (ι → M) where
  carrier := {v | ∀ t i, t • v i = ∑ j, ρ t i j • v j}
  add_mem' {v w} hv hw t i := by
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, hv t i, hw t i]
  zero_mem' t i := by simp
  smul_mem' c w hw t i := by
    simp only [Pi.smul_apply]
    rw [smul_comm, hw t i, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]

omit [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [Module.Finite 𝒪 T] [Module.Finite 𝒪 M]
  [IsTorsionFree 𝒪 M] in
theorem mem_eigenLatticeM {ι : Type*} [Fintype ι] (ρ : T → Matrix ι ι 𝒪) (v : ι → M) :
    v ∈ eigenLatticeM (M := M) ρ ↔ ∀ t i, t • v i = ∑ j, ρ t i j • v j := Iff.rfl

set_option maxHeartbeats 6400000 in

theorem main (χ : T →ₐ[𝒪] A) :
    finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker χ)) =
      finrank 𝒪 (T ⧸ RingHom.ker χ) *
        finrank A ↥(⨅ t : T, Module.End.eigenspace
          (((LinearMap.lsmul T M t).restrictScalars 𝒪).baseChange A) (χ t)) := by
  classical

  haveI : Nontrivial 𝒪 := (algebraMap 𝒪 A).domain_nontrivial
  set 𝔭 : Ideal T := RingHom.ker χ with h𝔭def
  haveI hprime : 𝔭.IsPrime := RingHom.ker_isPrime _
  set R : Type _ := T ⧸ 𝔭 with hRdef
  haveI : IsDomain R := Ideal.Quotient.isDomain _
  haveI : Module.Finite 𝒪 R :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 𝔭).toLinearMap Ideal.Quotient.mk_surjective
  haveI : IsTorsionFree 𝒪 R := isTorsionFree_quotient_ker χ
  haveI : IsNoetherian 𝒪 M := isNoetherian_of_isNoetherianRing_of_finite 𝒪 M
  set V : Submodule T M := Submodule.torsionBySet T M ↑𝔭 with hVdef
  haveI : Module.Finite 𝒪 ↥V := Module.Finite.of_injective (V.subtype.restrictScalars 𝒪)
    Subtype.val_injective
  haveI : IsTorsionFree 𝒪 ↥V := isTorsionFree_of_injective (V.subtype.restrictScalars 𝒪)
    Subtype.val_injective
  haveI : IsTorsionFree R ↥V := isTorsionFree_torsionBySet_quotient χ
  let φ : R →ₐ[𝒪] A := Ideal.kerLiftAlg χ
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective χ
  have hφmk : ∀ t, φ (Ideal.Quotient.mk 𝔭 t) = χ t := fun t => Ideal.kerLiftAlg_mk χ t

  haveI : Module.Free 𝒪 A := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex 𝒪 A
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype 𝒪 A
  let β : Module.Basis ι 𝒪 A := Module.Free.chooseBasis 𝒪 A
  have hApos : 0 < finrank 𝒪 A := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩
  let L : A → Matrix ι ι 𝒪 := fun a => Algebra.leftMulMatrix β a
  let ρ : T → Matrix ι ι 𝒪 := fun t => L (χ t)

  let Φ : A ⊗[𝒪] M ≃ₗ[𝒪] (ι → M) :=
    (TensorProduct.congr β.repr (LinearEquiv.refl 𝒪 M)).trans
      ((TensorProduct.finsuppScalarLeft 𝒪 M ι).trans (Finsupp.linearEquivFunOnFinite 𝒪 M ι))
  have hΦ : ∀ (x : A) (m : M) (i : ι), Φ (x ⊗ₜ m) i = β.repr x i • m := by
    intro x m i
    simp only [Φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      Finsupp.linearEquivFunOnFinite_apply, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  let f : T → (M →ₗ[𝒪] M) := fun t => (LinearMap.lsmul T M t).restrictScalars 𝒪
  have hf : ∀ t m, f t m = t • m := fun t m => rfl
  have hΦt : ∀ (t : T) (z : A ⊗[𝒪] M) (i : ι), Φ ((f t).baseChange A z) i = t • Φ z i := by
    intro t z
    induction z using TensorProduct.induction_on with
    | zero => intro i; simp
    | tmul x m => intro i; rw [LinearMap.baseChange_tmul, hΦ, hΦ, hf, smul_comm]
    | add z w hz hw => intro i; simp only [map_add, Pi.add_apply, hz i, hw i, smul_add]
  have hΦa : ∀ (a : A) (z : A ⊗[𝒪] M) (i : ι), Φ (a • z) i = ∑ j, L a i j • Φ z j := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => intro i; simp
    | tmul x m =>
        intro i
        rw [TensorProduct.smul_tmul', smul_eq_mul, hΦ]
        simp only [hΦ, smul_smul, ← Finset.sum_smul]
        congr 1
        have := congrFun (Algebra.leftMulMatrix_mulVec_repr β a x) i
        simp only [Matrix.mulVec, dotProduct] at this
        exact this.symm
    | add z w hz hw =>
        intro i
        simp only [smul_add, map_add, Pi.add_apply, hz i, hw i, Finset.sum_add_distrib]

  set W : Submodule A (A ⊗[𝒪] M) :=
    ⨅ t : T, Module.End.eigenspace ((f t).baseChange A) (χ t) with hWdef
  set W' : Submodule 𝒪 (ι → M) := eigenLatticeM (M := M) ρ with hW'def
  have hWW' : ∀ z, z ∈ W ↔ Φ z ∈ W' := by
    intro z
    rw [hWdef, Submodule.mem_iInf, mem_eigenLatticeM]
    constructor
    · intro h t i
      have := h t
      rw [Module.End.mem_eigenspace_iff] at this
      rw [← hΦt, this, hΦa]
    · intro h t
      rw [Module.End.mem_eigenspace_iff]
      apply Φ.injective
      funext i
      rw [hΦt, hΦa, h t i]

  let eW : ↥W ≃ₗ[𝒪] ↥W' :=
    { toFun := fun z => ⟨Φ (z : A ⊗[𝒪] M), (hWW' _).mp z.2⟩
      invFun := fun v => ⟨Φ.symm (v : ι → M), (hWW' _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact v.2)⟩
      left_inv := fun z => Subtype.ext (Φ.symm_apply_apply _)
      right_inv := fun v => Subtype.ext (Φ.apply_symm_apply _)
      map_add' := fun z w => Subtype.ext (by simp)
      map_smul' := fun c z => Subtype.ext (by simp) }
  haveI : IsNoetherian 𝒪 (ι → M) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
  haveI : Module.Finite 𝒪 ↥W' := Module.Finite.of_injective W'.subtype Subtype.val_injective
  haveI : IsTorsionFree 𝒪 (ι → M) := inferInstance
  haveI : IsTorsionFree 𝒪 ↥W' := isTorsionFree_of_injective W'.subtype Subtype.val_injective
  haveI : Module.Finite 𝒪 ↥W := Module.Finite.equiv eW.symm
  haveI : IsTorsionFree 𝒪 ↥W := isTorsionFree_of_injective (X := ↥W) eW.toLinearMap eW.injective
  haveI : Module.Free 𝒪 M := Module.free_of_finite_type_torsion_free'
  haveI : IsTorsionFree A ↥W :=
    isTorsionFree_of_injective (R := A) (X := ↥W) W.subtype Subtype.val_injective
  have hWrank : finrank 𝒪 ↥W = finrank A ↥W * finrank 𝒪 A :=
    finrank_eq_finrank_mul_finrank (𝒪 := 𝒪) (Q := A) (V := ↥W)
  have hWW'rank : finrank 𝒪 ↥W = finrank 𝒪 ↥W' := eW.finrank_eq

  have hW'V : ∀ v ∈ W', ∀ i, v i ∈ V := by
    intro v hv i
    rw [hVdef, Submodule.mem_torsionBySet_iff]
    rintro ⟨t, ht⟩
    rw [(mem_eigenLatticeM ρ v).mp hv t i]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ρ t = 0 := by
      show Algebra.leftMulMatrix β (χ t) = 0
      rw [(RingHom.mem_ker).mp ht, map_zero]
    rw [this, Matrix.zero_apply, zero_smul]
  set m := finrank R ↥V with hmdef
  have hVrank : finrank 𝒪 ↥V = m * finrank 𝒪 R :=
    finrank_eq_finrank_mul_finrank (𝒪 := 𝒪) (Q := R) (V := ↥V)
  obtain ⟨b, c₁, hb, hc₁, hbc⟩ := exists_linearIndependent_and_smul_mem_span (𝒪 := 𝒪) (Q := R)
    (V := ↥V) m hVrank
  set E : Submodule 𝒪 (ι → R) := eigenLattice (fun t : T => Ideal.Quotient.mk 𝔭 t) ρ with hEdef
  haveI : IsNoetherian 𝒪 (ι → R) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
  haveI : Module.Finite 𝒪 ↥E := Module.Finite.of_injective E.subtype Subtype.val_injective
  haveI : IsTorsionFree 𝒪 ↥E := isTorsionFree_of_injective E.subtype Subtype.val_injective
  haveI : Module.Free 𝒪 ↥E := Module.free_of_finite_type_torsion_free'

  have hsmulV : ∀ (t : T) (r : R) (x : ↥V), t • (r • x) = (Ideal.Quotient.mk 𝔭 t * r) • x := by
    intro t r x
    rw [mul_smul, Submodule.torsionBySet.mk_smul]

  let ξ : (Fin m → ↥E) → (ι → M) := fun w i => ((∑ k, ((w k : ι → R) i) • b k : ↥V) : M)
  have hξmem : ∀ w, ξ w ∈ W' := by
    intro w t i
    have key : t • (∑ k, ((w k : ι → R) i) • b k : ↥V) =
        ∑ j, ρ t i j • (∑ k, ((w k : ι → R) j) • b k : ↥V) := by
      calc t • (∑ k, ((w k : ι → R) i) • b k : ↥V)
          = ∑ k, (∑ j, ρ t i j • (w k : ι → R) j) • b k := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsmulV, ((mem_eigenLattice _ _ _).mp (w k).2 t i)]
        _ = ∑ k, ∑ j, ρ t i j • (((w k : ι → R) j) • b k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_assoc]
        _ = ∑ j, ρ t i j • (∑ k, ((w k : ι → R) j) • b k : ↥V) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.smul_sum]
    show t • ((∑ k, ((w k : ι → R) i) • b k : ↥V) : M) =
      ∑ j, ρ t i j • ((∑ k, ((w k : ι → R) j) • b k : ↥V) : M)
    rw [← Submodule.coe_smul, key]
    conv_lhs => rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul_of_tower]
  let Ξ : (Fin m → ↥E) →ₗ[𝒪] ↥W' :=
    { toFun := fun w => ⟨ξ w, hξmem w⟩
      map_add' := fun v w => by
        apply Subtype.ext; funext i
        show ((∑ k, (((v + w) k : ↥E) : ι → R) i • b k : ↥V) : M) =
          ((∑ k, ((v k : ι → R) i) • b k : ↥V) : M) + ((∑ k, ((w k : ι → R) i) • b k : ↥V) : M)
        rw [← Submodule.coe_add, ← Finset.sum_add_distrib]
        refine congrArg Subtype.val (Finset.sum_congr rfl fun k _ => ?_)
        rw [Pi.add_apply, Submodule.coe_add, Pi.add_apply, add_smul]
      map_smul' := fun c w => by
        apply Subtype.ext; funext i
        show ((∑ k, (((c • w) k : ↥E) : ι → R) i • b k : ↥V) : M) =
          c • ((∑ k, ((w k : ι → R) i) • b k : ↥V) : M)
        rw [← Submodule.coe_smul_of_tower, Finset.smul_sum]
        refine congrArg Subtype.val (Finset.sum_congr rfl fun k _ => ?_)
        rw [Pi.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_assoc] }
  have hΞapply : ∀ w i, ((Ξ w : ↥W') : ι → M) i = ((∑ k, ((w k : ι → R) i) • b k : ↥V) : M) :=
    fun w i => rfl
  have hΞinj : Function.Injective Ξ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    funext k
    apply Subtype.ext
    funext i
    have h1 : (∑ k, ((w k : ι → R) i) • b k : ↥V) = 0 := by
      have h0 : ((Ξ w : ↥W') : ι → M) i = 0 := by rw [hw]; rfl
      rw [hΞapply] at h0
      exact Subtype.ext h0
    have := (Fintype.linearIndependent_iff.mp hb) (fun k => (w k : ι → R) i) h1 k
    simpa using this
  have hΞsurj : ∀ v : ↥W', c₁ • v ∈ LinearMap.range Ξ := by
    intro v
    have hvV : ∀ i, (v : ι → M) i ∈ V := hW'V _ v.2
    choose g hg using fun i => hbc ⟨(v : ι → M) i, hvV i⟩

    have hgE : ∀ k, (fun i => g i k) ∈ E := by
      intro k t i

      have hv := (mem_eigenLatticeM ρ (v : ι → M)).mp v.2 t i
      have key : (∑ k, (Ideal.Quotient.mk 𝔭 t * g i k) • b k : ↥V) =
          ∑ k, (∑ j, ρ t i j • g j k) • b k := by
        have lhs : (∑ k, (Ideal.Quotient.mk 𝔭 t * g i k) • b k : ↥V) =
            t • (c₁ • (⟨(v : ι → M) i, hvV i⟩ : ↥V)) := by
          rw [hg i, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsmulV]
        have rhs : (∑ k, (∑ j, ρ t i j • g j k) • b k : ↥V) =
            ∑ j, ρ t i j • (c₁ • (⟨(v : ι → M) j, hvV j⟩ : ↥V)) := by
          calc (∑ k, (∑ j, ρ t i j • g j k) • b k : ↥V)
              = ∑ k, ∑ j, ρ t i j • (g j k • b k) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Finset.sum_smul]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [smul_assoc]
            _ = ∑ j, ρ t i j • (c₁ • (⟨(v : ι → M) j, hvV j⟩ : ↥V)) := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [hg j, Finset.smul_sum]
        rw [lhs, rhs]
        apply Subtype.ext
        simp only [Submodule.coe_smul_of_tower, Submodule.coe_sum, smul_comm t c₁, hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm]
      have hsub : (∑ k, (Ideal.Quotient.mk 𝔭 t * g i k - ∑ j, ρ t i j • g j k) • b k : ↥V) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]
      have := (Fintype.linearIndependent_iff.mp hb) _ hsub k
      exact sub_eq_zero.mp this
    refine ⟨fun k => ⟨fun i => g i k, hgE k⟩, ?_⟩
    apply Subtype.ext
    funext i
    rw [hΞapply, Submodule.coe_smul, Pi.smul_apply]
    have := congrArg (Subtype.val : ↥V → M) (hg i)
    rw [Submodule.coe_smul_of_tower] at this
    rw [this]
  have hW'E : finrank 𝒪 ↥W' = m * finrank 𝒪 ↥E := by
    rw [← finrank_eq_of_injective_of_smul_mem_range Ξ hΞinj c₁ hc₁ hΞsurj,
      Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

  set ER : Submodule 𝒪 (ι → R) := eigenLattice (fun r : R => r) (fun r => L (φ r)) with hERdef
  set ERT : Submodule 𝒪 (ι → R) := eigenLattice (fun r : R => r) (fun r => (L (φ r))ᵀ) with hERTdef
  have hEER : E = ER := by
    ext w
    rw [mem_eigenLattice, mem_eigenLattice]
    constructor
    · intro h r i
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [h t i]
      simp only [ρ, hφmk]
    · intro h t i
      have := h (Ideal.Quotient.mk 𝔭 t) i
      simp only [hφmk] at this
      exact this
  obtain ⟨i₀⟩ : Nonempty ι := β.index_nonempty
  set G : Matrix ι ι 𝒪 := Matrix.of fun i j => β.repr (β i * β j) i₀ with hGdef
  have hG : ∀ r : R, G * L (φ r) = (L (φ r))ᵀ * G := fun r => gram_mul_leftMulMatrix β i₀ (φ r)
  have hdet : G.det ≠ 0 := det_gram_ne_zero β i₀
  have hG' : ∀ r : R, G.adjugate * (L (φ r))ᵀ = ((L (φ r))ᵀ)ᵀ * G.adjugate := by
    intro r
    rw [Matrix.transpose_transpose]
    have h1 : G.det • (G.adjugate * (L (φ r))ᵀ) = G.det • (L (φ r) * G.adjugate) := by
      calc G.det • (G.adjugate * (L (φ r))ᵀ)
          = G.adjugate * (L (φ r))ᵀ * (G * G.adjugate) := by
            rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
        _ = G.adjugate * (G * L (φ r)) * G.adjugate := by
            rw [hG r]; simp only [Matrix.mul_assoc]
        _ = G.det • (L (φ r) * G.adjugate) := by
            rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
              smul_mul_assoc]
    ext i j
    have := congrArg (fun P : Matrix ι ι 𝒪 => P i j) h1
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hdet this
  have hdet' : G.adjugate.det ≠ 0 := by
    rw [Matrix.det_adjugate]; exact pow_ne_zero _ hdet
  have hle1 : finrank 𝒪 ↥ER ≤ finrank 𝒪 ↥ERT := finrank_eigenLattice_le _ _ G hG hdet
  have hle2 : finrank 𝒪 ↥ERT ≤ finrank 𝒪 ↥ER := by
    have h := finrank_eigenLattice_le (fun r : R => r) (fun r => (L (φ r))ᵀ) G.adjugate hG' hdet'
    have e : (fun t : R => (L (φ t))ᵀᵀ) = fun t => L (φ t) :=
      funext fun t => Matrix.transpose_transpose _
    rw [e] at h
    exact h
  have hERT : finrank 𝒪 ↥ERT = finrank 𝒪 A := finrank_eigenLattice_transpose_eq φ hφ β
  have hErank : finrank 𝒪 ↥E = finrank 𝒪 A := by
    rw [hEER]; exact le_antisymm (hle1.trans hERT.le) (hERT.ge.trans hle2)

  have h1 : finrank A ↥W * finrank 𝒪 A = m * finrank 𝒪 A := by
    rw [← hWrank, hWW'rank, hW'E, hErank]
  have h2 : finrank A ↥W = m := Nat.eq_of_mul_eq_mul_right hApos h1
  show finrank 𝒪 ↥V = finrank 𝒪 R * finrank A ↥W
  rw [h2, hVrank, mul_comm]

end Final

end FKAlg2Sol

theorem solution
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    [Module.IsTorsionFree 𝒪 A]
    (χ : T →ₐ[𝒪] A) :
    Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker χ)) =
      Module.finrank 𝒪 (T ⧸ RingHom.ker χ) *
        Module.finrank A ↥(⨅ t : T, Module.End.eigenspace
          (((LinearMap.lsmul T M t).restrictScalars 𝒪).baseChange A) (χ t)) :=
  FKAlg2Sol.main χ

end S_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange
end P2MW
export P2MW.S_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange (solution)
