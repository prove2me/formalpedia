-- Prove2me | solution 1 for Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/466eff5e-aedc-577e-a4f2-0c03b5f5605c

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Order.SupIndep
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic

set_option autoImplicit false
set_option maxHeartbeats 6400000

open Module

namespace ALG

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hstab : ∀ a ∈ A, ∀ (i : ι), ∀ v ∈ V i, a v ∈ V i)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)

include hVtop he₁ he₀ in
theorem decomp [DecidableEq ι] (v : W) :
    (∑ i, (e i : Module.End K W) v = v) ∧ ∀ i, (e i : Module.End K W) v ∈ V i := by
  have hv : v ∈ ⨆ i, V i := by rw [hVtop]; trivial
  refine Submodule.iSup_induction V
    (motive := fun v => (∑ i, (e i : Module.End K W) v = v) ∧ ∀ i, (e i : Module.End K W) v ∈ V i)
    hv ?_ ?_ ?_
  · intro j x hx
    constructor
    · rw [Finset.sum_eq_single j (fun i _ hij => he₀ i j (Ne.symm hij) x hx)
        (fun h => absurd (Finset.mem_univ j) h), he₁ j x hx]
    · intro i
      by_cases hij : j = i
      · subst hij; rw [he₁ j x hx]; exact hx
      · rw [he₀ i j hij x hx]; exact Submodule.zero_mem _
  · simp
  · intro x y hx hy
    constructor
    · simp only [map_add, Finset.sum_add_distrib, hx.1, hy.1]
    · intro i; rw [map_add]; exact Submodule.add_mem _ (hx.2 i) (hy.2 i)

include hVtop he₁ he₀ in
theorem e_apply_mem (i : ι) (v : W) : (e i : Module.End K W) v ∈ V i := by
  classical
  exact (decomp V hVtop A e he₁ he₀ v).2 i

include hVtop he₁ he₀ in
theorem sum_e_apply (v : W) : ∑ i, (e i : Module.End K W) v = v := by
  classical
  exact (decomp V hVtop A e he₁ he₀ v).1

def w0 : W := ∑ i, w i

include he₁ he₀ hw in
theorem e_w0 [DecidableEq ι] (i : ι) : (e i : Module.End K W) (w0 w) = w i := by
  unfold w0
  rw [map_sum, Finset.sum_eq_single i (fun j _ hji => he₀ i j hji _ (hw j))
    (fun h => absurd (Finset.mem_univ i) h), he₁ i _ (hw i)]

def ψ : ↥A →ₗ[↥A] W where
  toFun a := (a : Module.End K W) (w0 w)
  map_add' a b := by simp
  map_smul' c a := by
    simp only [smul_eq_mul, Subalgebra.coe_mul, Module.End.mul_apply, RingHom.id_apply]
    rfl

theorem ψ_apply (a : ↥A) : ψ A w a = (a : Module.End K W) (w0 w) := rfl

include hVtop he₁ he₀ hw hcyc in
theorem ψ_surjective : Function.Surjective (ψ A w) := by
  classical
  intro v
  have hdec := decomp V hVtop A e he₁ he₀ v
  choose a ha using fun i => hcyc i _ (hdec.2 i)
  refine ⟨∑ i, a i * e i, ?_⟩
  rw [ψ_apply, AddSubmonoidClass.coe_finset_sum, LinearMap.sum_apply]
  conv_rhs => rw [← hdec.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_mul, Module.End.mul_apply, e_w0 V A e he₁ he₀ w hw i, ha i]

include hVtop hcomm he₁ he₀ hw hcyc in
theorem ψ_injective : Function.Injective (ψ A w) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  rw [ψ_apply] at ha

  have hwi : ∀ i, (a : Module.End K W) (w i) = 0 := by
    intro i
    have h1 : (a : Module.End K W) (w i) = ((a : Module.End K W) * (e i : Module.End K W)) (w0 w) := by
      rw [Module.End.mul_apply, e_w0 V A e he₁ he₀ w hw i]
    rw [h1, hcomm _ a.2 _ (e i).2, Module.End.mul_apply, ha, map_zero]

  have hVi : ∀ i, ∀ v ∈ V i, (a : Module.End K W) v = 0 := by
    intro i v hv
    obtain ⟨b, hb⟩ := hcyc i v hv
    rw [← hb, ← Module.End.mul_apply, hcomm _ a.2 _ b.2, Module.End.mul_apply, hwi i, map_zero]

  apply Subtype.ext
  refine LinearMap.ext fun v => ?_
  rw [← sum_e_apply V hVtop A e he₁ he₀ v, map_sum]
  simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun i _ => hVi i _ (e_apply_mem V hVtop A e he₁ he₀ i v)

end ALG

namespace ALG

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)

noncomputable def ψe : ↥A ≃ₗ[↥A] W :=
  LinearEquiv.ofBijective (ψ A w)
    ⟨ψ_injective V hVtop A hcomm e he₁ he₀ w hw hcyc, ψ_surjective V hVtop A e he₁ he₀ w hw hcyc⟩

include V hVtop hcomm e he₁ he₀ w hw hcyc in
theorem nonempty_basis : Nonempty (Module.Basis (Fin 1) ↥A W) :=
  ⟨(Module.Basis.singleton (Fin 1) ↥A).map (ψe V hVtop A hcomm e he₁ he₀ w hw hcyc)⟩

include hVtop he₁ he₀ in
theorem sum_e_eq_one : ∑ i, e i = (1 : ↥A) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sum_apply, Module.End.one_apply]
  exact sum_e_apply V hVtop A e he₁ he₀ v

include hVtop he₁ he₀ in
theorem e_mul_e_self (i : ι) : e i * e i = e i := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul]
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply]
  exact he₁ i _ (e_apply_mem V hVtop A e he₁ he₀ i v)

include hVtop he₁ he₀ in
theorem exists_chi_e_eq_one (χ : ↥A →ₐ[K] K) : ∃ i, χ (e i) = 1 := by
  classical
  by_contra h
  push Not at h
  have h01 : ∀ i, χ (e i) = 0 := by
    intro i
    have hsq : χ (e i) * χ (e i) = χ (e i) := by rw [← map_mul, e_mul_e_self V hVtop A e he₁ he₀ i]
    have : χ (e i) * (χ (e i) - 1) = 0 := by rw [mul_sub, mul_one, hsq, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact h0
    · exact absurd (sub_eq_zero.mp h1) (h i)
  have := congrArg χ (sum_e_eq_one V hVtop A e he₁ he₀)
  rw [map_sum, map_one] at this
  simp [h01] at this

def Eig (χ : ↥A →ₐ[K] K) : Submodule K W :=
  ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)

theorem mem_Eig {χ : ↥A →ₐ[K] K} {v : W} : v ∈ Eig A χ ↔ ∀ a : ↥A, (a : Module.End K W) v = χ a • v := by
  simp [Eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

include hVtop he₁ he₀ in
theorem Eig_le (χ : ↥A →ₐ[K] K) {i : ι} (hi : χ (e i) = 1) : Eig A χ ≤ V i := by
  intro v hv
  rw [mem_Eig] at hv
  have := hv (e i)
  rw [hi, one_smul] at this
  rw [← this]
  exact e_apply_mem V hVtop A e he₁ he₀ i v

include hVtop he₁ he₀ in
theorem finrank_Eig_le (χ : ↥A →ₐ[K] K)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Module.finrank K ↥(Eig A χ) ≤ 1 := by
  obtain ⟨i, hi⟩ := exists_chi_e_eq_one V hVtop A e he₁ he₀ χ
  have h : Eig A χ ≤ V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a) :=
    le_inf (Eig_le V hVtop A e he₁ he₀ χ hi) le_rfl
  exact (Submodule.finrank_mono h).trans (hle i χ)

end ALG

namespace ALG

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)

abbrev commRing : CommRing ↥A :=
  { (inferInstance : Ring ↥A) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }

include hcomm in

theorem exists_socle (χ : ↥A →ₐ[K] K) : ∃ b : ↥A, b ≠ 0 ∧ ∀ a : ↥A, a * b = χ a • b := by
  classical
  letI : CommRing ↥A := commRing A hcomm
  haveI : FiniteDimensional K ↥A :=
    FiniteDimensional.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : IsNoetherian ↥A ↥A := isNoetherian_of_tower K inferInstance
  haveI : IsArtinian K ↥A := inferInstance
  set m : Ideal ↥A := RingHom.ker χ with hm

  let f : ℕ →o (Submodule K ↥A)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual ((m ^ n).restrictScalars K), fun i j hij => by
      change (m ^ j).restrictScalars K ≤ (m ^ i).restrictScalars K
      exact fun x hx => Ideal.pow_le_pow_right hij hx⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  have hstab : m ^ N = m ^ (N + 1) := by
    have := hN (N + 1) (Nat.le_succ N)
    exact Submodule.restrictScalars_injective K _ _ (OrderDual.toDual.injective this)

  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (m ^ N)
    (IsNoetherian.noetherian _) (by change m ^ N ≤ m * m ^ N; rw [← pow_succ', ← hstab])
  have hχr : χ r = 1 := by
    have : χ (r - 1) = 0 := (RingHom.mem_ker).mp hr1
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hr0 : r ≠ 0 := by rintro rfl; rw [map_zero] at hχr; exact zero_ne_one hχr

  have hP : ∃ n : ℕ, ∀ x ∈ m ^ n, r * x = 0 := ⟨N, fun x hx => hr2 x hx⟩
  set n₀ := Nat.find hP with hn₀def
  have hn₀ : ∀ x ∈ m ^ n₀, r * x = 0 := Nat.find_spec hP
  have hn₀ne : n₀ ≠ 0 := by
    intro h
    have := hn₀ 1 (by rw [h, pow_zero, Ideal.one_eq_top]; trivial)
    rw [mul_one] at this
    exact hr0 this
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn₀ne
  have hmin : ¬ ∀ x ∈ m ^ n', r * x = 0 := Nat.find_min hP (by rw [← hn₀def, hn']; exact Nat.lt_succ_self n')
  push Not at hmin
  obtain ⟨x, hx, hrx⟩ := hmin
  refine ⟨r * x, hrx, fun a => ?_⟩
  have ha' : a - algebraMap K ↥A (χ a) ∈ m := by
    rw [hm, RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  have hkill : (a - algebraMap K ↥A (χ a)) * (r * x) = 0 := by
    rw [mul_left_comm]
    apply hn₀
    rw [hn', pow_succ']
    exact Ideal.mul_mem_mul ha' hx
  calc a * (r * x) = (a - algebraMap K ↥A (χ a)) * (r * x) + algebraMap K ↥A (χ a) * (r * x) := by ring
    _ = χ a • (r * x) := by rw [hkill, zero_add, Algebra.smul_def]

include hVtop hcomm he₁ he₀ hw hcyc in
theorem exists_mem_Eig_ne_zero (χ : ↥A →ₐ[K] K) : ∃ v ∈ Eig A χ, v ≠ 0 := by
  obtain ⟨b, hb0, hb⟩ := exists_socle A hcomm χ
  refine ⟨ψ A w b, ?_, ?_⟩
  · rw [mem_Eig]
    intro a
    rw [ψ_apply, ← Module.End.mul_apply, ← Subalgebra.coe_mul, hb a, Subalgebra.coe_smul,
      LinearMap.smul_apply]
  · intro h
    apply hb0
    apply ψ_injective V hVtop A hcomm e he₁ he₀ w hw hcyc
    rw [h, map_zero]

include hVtop hcomm he₁ he₀ hw hcyc in
theorem finrank_Eig_eq_one (χ : ↥A →ₐ[K] K)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Module.finrank K ↥(Eig A χ) = 1 := by
  have h1 := finrank_Eig_le V hVtop A e he₁ he₀ χ hle
  obtain ⟨v, hv, hv0⟩ := exists_mem_Eig_ne_zero V hVtop A hcomm e he₁ he₀ w hw hcyc χ
  have h2 : 0 < Module.finrank K ↥(Eig A χ) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  omega

end ALG

theorem solution
    {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (V : ι → Submodule K W) (hVind : iSupIndep V) (hVtop : iSup V = ⊤)
    (A : Subalgebra K (Module.End K W))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hstab : ∀ a ∈ A, ∀ (i : ι), ∀ v ∈ V i, a v ∈ V i)
    (e : ι → ↥A) (he₁ : ∀ (i : ι), ∀ v ∈ V i, (e i : Module.End K W) v = v)
    (he₀ : ∀ (i j : ι), j ≠ i → ∀ v ∈ V j, (e i : Module.End K W) v = 0)
    (w : ι → W) (hw : ∀ i, w i ∈ V i)
    (hcyc : ∀ (i : ι), ∀ v ∈ V i, ∃ a : ↥A, (a : Module.End K W) (w i) = v)
    (hle : ∀ (i : ι) (χ : ↥A →ₐ[K] K),
      Module.finrank K ↥(V i ⊓ ⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) ≤ 1) :
    Nonempty (Module.Basis (Fin 1) ↥A W) ∧
    ∀ χ : ↥A →ₐ[K] K,
      Module.finrank K ↥(⨅ a : ↥A, Module.End.eigenspace (a : Module.End K W) (χ a)) = 1 :=
  ⟨ALG.nonempty_basis V hVtop A hcomm e he₁ he₀ w hw hcyc,
   fun χ => ALG.finrank_Eig_eq_one V hVtop A hcomm e he₁ he₀ w hw hcyc χ hle⟩

end S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic
end P2MW
export P2MW.S_Module_End_nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic (solution)
