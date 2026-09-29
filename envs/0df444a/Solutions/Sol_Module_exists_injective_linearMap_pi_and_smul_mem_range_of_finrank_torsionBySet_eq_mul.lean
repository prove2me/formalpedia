-- Prove2me | solution 1 for Module.exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/31022632-3831-5338-a137-5a4b8035dd9c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FKAlgSol

open Module Polynomial

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

set_option maxHeartbeats 3200000 in

theorem main
    {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, Algebra 𝒪 (A i)]
    [∀ i, IsTorsionFree 𝒪 (A i)]
    (χ : ∀ i, T →ₐ[𝒪] A i) (hker : ⨅ i, RingHom.ker (χ i) = ⊥)
    (a : 𝒪) (ha : a ≠ 0) (hsurj : ∀ y : ∀ i, A i, ∃ x : T, ∀ i, χ i x = a • y i)
    (d : ℕ)
    (hrank : ∀ i, finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker (χ i))) =
      d * finrank 𝒪 (T ⧸ RingHom.ker (χ i))) :
    ∃ (f : (Fin d → T) →ₗ[T] M) (c : 𝒪), c ≠ 0 ∧ Function.Injective f ∧
      ∀ m : M, c • m ∈ LinearMap.range f := by
  classical

  haveI hprime : ∀ i, (RingHom.ker (χ i)).IsPrime := fun i => RingHom.ker_isPrime _
  haveI : ∀ i, IsDomain (T ⧸ RingHom.ker (χ i)) := fun i => Ideal.Quotient.isDomain _
  haveI : ∀ i, Module.Finite 𝒪 (T ⧸ RingHom.ker (χ i)) := fun i =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 (RingHom.ker (χ i))).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : ∀ i, IsTorsionFree 𝒪 (T ⧸ RingHom.ker (χ i)) := fun i => isTorsionFree_quotient_ker (χ i)
  haveI : IsNoetherian 𝒪 M := isNoetherian_of_isNoetherianRing_of_finite 𝒪 M
  let V : ι → Submodule T M := fun i => Submodule.torsionBySet T M ↑(RingHom.ker (χ i))
  haveI : ∀ i, Module.Finite 𝒪 ↥(V i) := fun i =>
    Module.Finite.of_injective ((V i).subtype.restrictScalars 𝒪) Subtype.val_injective
  haveI : ∀ i, IsTorsionFree 𝒪 ↥(V i) := fun i =>
    isTorsionFree_of_injective ((V i).subtype.restrictScalars 𝒪) Subtype.val_injective
  haveI : ∀ i, IsTorsionFree (T ⧸ RingHom.ker (χ i)) ↥(V i) := fun i =>
    isTorsionFree_torsionBySet_quotient (χ i)

  have hzero : ∀ t : T, (∀ i, χ i t = 0) → t = 0 := by
    intro t ht
    have : t ∈ (⨅ i, RingHom.ker (χ i) : Ideal T) := Ideal.mem_iInf.mpr fun i => ht i
    rwa [hker, Ideal.mem_bot] at this

  choose x hx using fun i => hsurj (Pi.single i 1)
  have hxii : ∀ i, χ i (x i) = algebraMap 𝒪 (A i) a := fun i => by
    rw [hx i i, Pi.single_eq_same, Algebra.algebraMap_eq_smul_one]
  have hxij : ∀ i j, i ≠ j → χ j (x i) = 0 := fun i j hij => by
    rw [hx i j, Pi.single_eq_of_ne' hij, smul_zero]
  have hxmem : ∀ i j, i ≠ j → x i ∈ RingHom.ker (χ j) := fun i j hij =>
    (RingHom.mem_ker).mpr (hxij i j hij)
  have hxsum : ∑ i, x i = algebraMap 𝒪 T a := by
    rw [← sub_eq_zero]
    refine hzero _ fun j => ?_
    rw [map_sub, map_sum, AlgHom.commutes, Finset.sum_eq_single j (fun i _ hij => hxij i j hij)
      (fun h => absurd (Finset.mem_univ j) h), hxii, sub_self]

  have hxkill : ∀ i j, i ≠ j → ∀ v : M, v ∈ V j → x i • v = 0 := fun i j hij v hv =>
    (Submodule.mem_torsionBySet_iff _ _).mp hv ⟨x i, hxmem i j hij⟩
  have hxact : ∀ i (v : M), v ∈ V i → x i • v = a • v := by
    intro i v hv
    have : (∑ j, x j) • v = a • v := by rw [hxsum, algebraMap_smul]
    rw [Finset.sum_smul, Finset.sum_eq_single i (fun j _ hji => hxkill j i hji v hv)
      (fun h => absurd (Finset.mem_univ i) h)] at this
    exact this

  have hxV : ∀ i (m : M), x i • m ∈ V i := by
    intro i m
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨t, ht⟩
    rw [smul_smul]
    have : t * x i = 0 := by
      refine hzero _ fun j => ?_
      rw [map_mul]
      by_cases hij : i = j
      · subst hij; rw [(RingHom.mem_ker).mp ht, zero_mul]
      · rw [hxij i j hij, mul_zero]
    rw [this, zero_smul]

  have hpoint : ∀ i, ∃ (b : Fin d → ↥(V i)) (c : 𝒪),
      LinearIndependent (T ⧸ RingHom.ker (χ i)) b ∧ c ≠ 0 ∧
        ∀ v : ↥(V i), ∃ g : Fin d → T ⧸ RingHom.ker (χ i), c • v = ∑ k, g k • b k := fun i =>
    exists_linearIndependent_and_smul_mem_span (𝒪 := 𝒪) (Q := T ⧸ RingHom.ker (χ i))
      (V := ↥(V i)) d (hrank i)
  choose b c hb hc hbc using hpoint

  let m : Fin d → M := fun k => ∑ i, (b i k : M)
  let f : (Fin d → T) →ₗ[T] M :=
    ∑ k, (LinearMap.proj k : (Fin d → T) →ₗ[T] T).smulRight (m k)
  have hf : ∀ t : Fin d → T, f t = ∑ k, t k • m k := fun t => by
    simp only [f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

  have hxm : ∀ i k, x i • m k = a • (b i k : M) := by
    intro i k
    simp only [m, Finset.smul_sum]
    rw [Finset.sum_eq_single i (fun j _ hji => hxkill i j (Ne.symm hji) _ (b j k).2)
      (fun h => absurd (Finset.mem_univ i) h)]
    exact hxact i _ (b i k).2
  have hxf : ∀ i (t : Fin d → T), x i • f t = a • ∑ k, t k • (b i k : M) := by
    intro i t
    rw [hf, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, mul_comm, ← smul_smul, hxm, smul_comm]

  have hsumV : ∀ i (t : Fin d → T),
      ((∑ k, (Ideal.Quotient.mk (RingHom.ker (χ i)) (t k)) • b i k : ↥(V i)) : M) =
        ∑ k, t k • (b i k : M) := by
    intro i t
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.torsionBySet.mk_smul]
    rfl
  refine ⟨f, a * a * ∏ i, c i, ?_, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero ha ha) (Finset.prod_ne_zero_iff.mpr fun i _ => hc i)
  ·
    rw [injective_iff_map_eq_zero]
    intro t ht
    funext k
    refine hzero _ fun i => ?_
    have h1 : a • ∑ k, t k • (b i k : M) = 0 := by rw [← hxf, ht, smul_zero]
    have h2 : ∑ k, t k • (b i k : M) = 0 := (smul_eq_zero_iff_right ha).mp h1
    have h3 : (∑ k, (Ideal.Quotient.mk (RingHom.ker (χ i)) (t k)) • b i k : ↥(V i)) = 0 := by
      apply Subtype.ext
      rw [hsumV, h2, Submodule.coe_zero]
    have h4 := (Fintype.linearIndependent_iff.mp (hb i)) _ h3 k
    exact (RingHom.mem_ker).mp (Ideal.Quotient.eq_zero_iff_mem.mp h4)
  ·
    intro m₀

    have hstep : ∀ i, a • (c i • (x i • m₀)) ∈ LinearMap.range f := by
      intro i
      obtain ⟨g, hg⟩ := hbc i ⟨x i • m₀, hxV i m₀⟩

      choose t ht using fun k => Ideal.Quotient.mk_surjective (g k)
      refine ⟨fun k => t k * x i, ?_⟩
      have hcoe : c i • (x i • m₀) = ∑ k, t k • (b i k : M) := by
        have := congrArg (Subtype.val : ↥(V i) → M) hg
        rw [Submodule.coe_smul_of_tower] at this
        rw [this, ← hsumV]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ht]
      rw [hf]
      calc ∑ k, (t k * x i) • m k = ∑ k, t k • (x i • m k) := by
            refine Finset.sum_congr rfl fun k _ => ?_; rw [← smul_smul]
        _ = a • ∑ k, t k • (b i k : M) := by
            rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
            rw [hxm, smul_comm]
        _ = a • (c i • (x i • m₀)) := by rw [hcoe]
    have : (a * a * ∏ i, c i) • m₀ = ∑ i, (∏ j ∈ Finset.univ.erase i, c j) • (a • (c i • (x i • m₀))) := by
      have h1 : (a * a * ∏ i, c i) • m₀ = (a * ∏ i, c i) • ((∑ i, x i) • m₀) := by
        rw [hxsum, algebraMap_smul, smul_smul]
        ring_nf
      rw [h1, Finset.sum_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (hstep i)

end Main

end FKAlgSol

theorem solution
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, Algebra 𝒪 (A i)]
    [∀ i, Module.IsTorsionFree 𝒪 (A i)]
    (χ : ∀ i, T →ₐ[𝒪] A i) (hker : ⨅ i, RingHom.ker (χ i) = ⊥)
    (a : 𝒪) (ha : a ≠ 0) (hsurj : ∀ y : ∀ i, A i, ∃ x : T, ∀ i, χ i x = a • y i)
    (d : ℕ)
    (hrank : ∀ i, Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker (χ i))) =
      d * Module.finrank 𝒪 (T ⧸ RingHom.ker (χ i))) :
    ∃ (f : (Fin d → T) →ₗ[T] M) (c : 𝒪), c ≠ 0 ∧ Function.Injective f ∧
      ∀ m : M, c • m ∈ LinearMap.range f :=
  FKAlgSol.main χ hker a ha hsurj d hrank

end S_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul
end P2MW
export P2MW.S_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul (solution)
