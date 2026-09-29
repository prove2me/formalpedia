-- Prove2me | solution 1 for MvFormalGroup.exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/21265e67-4fcd-5fac-b650-9c2ce48ed38d

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete

open scoped TensorProduct
open MvPowerSeries

universe u

namespace P2mTorsionHopf

abbrev pI (𝓞 : Type*) [CommRing 𝓞] (p : ℕ) (T : Type*) [CommRing T] [Algebra 𝓞 T] : Ideal T :=
  Ideal.span {algebraMap 𝓞 T (p : 𝓞)}

theorem pI_eq (𝓞 : Type*) [CommRing 𝓞] (p : ℕ) (T : Type*) [CommRing T] [Algebra 𝓞 T] :
    pI 𝓞 p T = Ideal.span {(p : T)} := by
  rw [pI, map_natCast]

section Complete

variable (𝓞 : Type*) [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (B : Type*) [CommRing B] [Algebra 𝓞 B]

theorem mem_span_pow_smul_top_iff {S : Type*} [CommRing S] (a : S) (n : ℕ) (x : S) :
    x ∈ (Ideal.span {a}) ^ n • (⊤ : Submodule S S) ↔ ∃ y, x = a ^ n * y := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm _ _⟩

theorem isAdicComplete_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝓞 B) :
    IsAdicComplete (pI 𝓞 p B) B := by
  classical
  set a : B := algebraMap 𝓞 B (p : 𝓞) with ha_def
  have hpB : ∀ (n : ℕ) (y : B), a ^ n * y = ((p : 𝓞) ^ n) • y := fun n y => by
    rw [Algebra.smul_def, map_pow]

  have hcoord : ∀ (n : ℕ) (x : B), (∃ y, x = a ^ n * y) → ∀ i, ∃ c : 𝓞, b.repr x i = (p : 𝓞) ^ n * c := by
    rintro n x ⟨y, rfl⟩ i
    refine ⟨b.repr y i, ?_⟩
    rw [hpB, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hH : IsHausdorff (pI 𝓞 p B) B := by
    refine ⟨fun x hx => ?_⟩
    have hx' : ∀ n, ∃ y, x = a ^ n * y := fun n => by
      have := hx n
      rw [SModEq.zero, mem_span_pow_smul_top_iff] at this
      exact this
    rw [← b.linearCombination_repr x]
    have : b.repr x = 0 := by
      ext i
      rw [Finsupp.zero_apply]
      refine IsHausdorff.haus' (I := Ideal.span {(p : 𝓞)}) (b.repr x i) fun n => ?_
      rw [SModEq.zero, mem_span_pow_smul_top_iff]
      exact hcoord n x (hx' n) i
    rw [this, map_zero]
  have hP : IsPrecomplete (pI 𝓞 p B) B := by
    refine ⟨fun f hf => ?_⟩
    have hf' : ∀ {m n : ℕ}, m ≤ n → ∃ y, f m - f n = a ^ m * y := fun {m n} hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, mem_span_pow_smul_top_iff] at this
      exact this

    have hc : ∀ i, ∀ {m n : ℕ}, m ≤ n →
        b.repr (f m) i ≡ b.repr (f n) i [SMOD (Ideal.span {(p : 𝓞)}) ^ m • (⊤ : Submodule 𝓞 𝓞)] := by
      intro i m n hmn
      rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]
      obtain ⟨c, hc⟩ := hcoord m _ (hf' hmn) i
      exact ⟨c, by rw [← hc, map_sub, Finsupp.sub_apply]⟩
    choose c hcl using fun i => IsPrecomplete.prec' (I := Ideal.span {(p : 𝓞)}) (fun n => b.repr (f n) i) (hc i)
    refine ⟨∑ i, c i • b i, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]
    have hd : ∀ i, ∃ e : 𝓞, b.repr (f n) i - c i = (p : 𝓞) ^ n * e := fun i => by
      have := hcl i n
      rw [SModEq.sub_mem, mem_span_pow_smul_top_iff] at this
      exact this
    choose e he using hd
    refine ⟨∑ i, e i • b i, ?_⟩
    conv_lhs => rw [← b.sum_repr (f n)]
    rw [← Finset.sum_sub_distrib, hpB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, he, smul_smul]
  exact IsAdicComplete.mk

end Complete

section Uniq

variable {𝓞 : Type*} [CommRing 𝓞] {S : Type*} [CommRing S] [Algebra 𝓞 S] {σ : Type*} [Finite σ]

theorem exists_pow_span_X_le (J : Ideal S) (ψ : MvPowerSeries σ 𝓞 →ₐ[𝓞] S)
    (hψ : ∀ s, ψ (X s) ∈ J.radical) : ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, ∀ G ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ (N * n), ψ G ∈ J ^ n := by
  classical
  set IX : Ideal (MvPowerSeries σ 𝓞) := Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))
  have hle : IX.map (ψ : MvPowerSeries σ 𝓞 →+* S) ≤ J.radical := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hψ s
  have hfg : (IX.map (ψ : MvPowerSeries σ 𝓞 →+* S)).FG :=
    Ideal.FG.map (Submodule.fg_span (Set.finite_range _)) _
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle hfg
  refine ⟨N + 1, Nat.succ_pos N, fun n G hG => ?_⟩
  have h1 : ψ G ∈ (IX ^ ((N + 1) * n)).map (ψ : MvPowerSeries σ 𝓞 →+* S) := Ideal.mem_map_of_mem _ hG
  rw [Ideal.map_pow, pow_mul] at h1
  have h2 : (IX.map (ψ : MvPowerSeries σ 𝓞 →+* S)) ^ (N + 1) ≤ J :=
    (Ideal.pow_le_pow_right (Nat.le_succ N)).trans hN
  exact Ideal.pow_right_mono h2 n h1

theorem algHom_eq_adicEval (J : Ideal S) [IsAdicComplete J S] (ψ : MvPowerSeries σ 𝓞 →ₐ[𝓞] S)
    (hψ : ∀ s, ψ (X s) ∈ J.radical) (G : MvPowerSeries σ 𝓞) :
    ψ G = MvFormalGroup.adicEval J (fun s => ψ (X s)) G := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  let E : MvPowerSeries σ 𝓞 →ₐ[𝓞] S := MvFormalGroup.adicEvalAlgHom J hψ
  have hE : ∀ G, E G = MvFormalGroup.adicEval J (fun s => ψ (X s)) G :=
    fun G => congrFun (MvFormalGroup.coe_adicEvalAlgHom J hψ) G
  rw [← hE]

  have hpoly : ∀ P : MvPolynomial σ 𝓞, ψ (P : MvPowerSeries σ 𝓞) = E (P : MvPowerSeries σ 𝓞) := by
    intro P
    have : ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom 𝓞) =
        E.comp (MvPolynomial.coeToMvPowerSeries.algHom 𝓞) := by
      refine MvPolynomial.algHom_ext fun s => ?_
      simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
        MvPowerSeries.map_id, RingHom.id_apply, MvPolynomial.coe_X]
      rw [hE, MvFormalGroup.adicEval_X]
    have h := congrArg (fun χ => χ P) this
    simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPowerSeries.map_id] using h

  have hEX : ∀ s, E (X s) ∈ J.radical := fun s => by rw [hE, MvFormalGroup.adicEval_X]; exact hψ s
  obtain ⟨N₁, hN₁, h₁⟩ := exists_pow_span_X_le J ψ hψ
  obtain ⟨N₂, hN₂, h₂⟩ := exists_pow_span_X_le J E hEX

  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  set M := N₁ * N₂ * n
  set P := truncTotal M G
  have hR : G - (P : MvPowerSeries σ 𝓞) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ M := by
    refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero M _ fun m hm => ?_
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hm, sub_self]
  have hψR : ψ (G - P) ∈ J ^ n := by
    refine h₁ n _ ?_
    have : Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ M ≤
        Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ (N₁ * n) :=
      Ideal.pow_le_pow_right (Nat.mul_le_mul_right n (Nat.le_mul_of_pos_right N₁ hN₂))
    exact this hR
  have hER : E (G - P) ∈ J ^ n := by
    refine h₂ n _ ?_
    have : Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ M ≤
        Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞)) ^ (N₂ * n) :=
      Ideal.pow_le_pow_right (Nat.mul_le_mul_right n (Nat.le_mul_of_pos_left N₂ hN₁))
    exact this hR
  have : ψ G - E G = ψ (G - P) - E (G - P) := by rw [map_sub, map_sub, hpoly P]; ring
  rw [this]
  exact Submodule.sub_mem _ hψR hER

end Uniq

section Level

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]

def Lev (n : ℕ) : Type u := MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n))

variable (n : ℕ)

noncomputable scoped instance Lev.instCommRing : CommRing (Lev Φ n) :=
  inferInstanceAs (CommRing (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n))))

p2m_reactivate "P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.P2mTorsionHopf.Lev"
noncomputable scoped instance Lev.instAlgebra : Algebra 𝓞 (Lev Φ n) :=
  inferInstanceAs (Algebra 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n))))

p2m_reactivate "P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.P2mTorsionHopf.Lev"

noncomputable def πL : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] Lev Φ n :=
  Ideal.Quotient.mkₐ 𝓞 (Ideal.span (Set.range (Φ.nthSeries n)))

noncomputable def xL : Fin d → Lev Φ n := fun i => πL Φ n (X i)

omit [Φ.IsComm] in
theorem πL_apply (G : MvPowerSeries (Fin d) 𝓞) :
    πL Φ n G = (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.nthSeries n))) G : Lev Φ n) := rfl

omit [Φ.IsComm] in
theorem πL_eq_zero_iff (G : MvPowerSeries (Fin d) 𝓞) :
    πL Φ n G = 0 ↔ G ∈ Ideal.span (Set.range (Φ.nthSeries n)) :=
  Ideal.Quotient.eq_zero_iff_mem

omit [Φ.IsComm] in
theorem ker_πL : RingHom.ker (πL Φ n) = Ideal.span (Set.range (Φ.nthSeries n)) :=
  Ideal.Quotient.mkₐ_ker 𝓞 _

omit [Φ.IsComm] in
theorem πL_surjective : Function.Surjective (πL Φ n) := Ideal.Quotient.mk_surjective

omit [Φ.IsComm] in
theorem πL_X (i : Fin d) : πL Φ n (X i) = xL Φ n i := rfl

def NilHyp : Prop := ∀ i : Fin d, ∃ N : ℕ, (X i : MvPowerSeries (Fin d) 𝓞) ^ N ∈
  Ideal.span (Set.range (Φ.nthSeries n)) ⊔ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)}

variable {p Φ n}

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
theorem xL_mem_radical (hnil : NilHyp p Φ n) (i : Fin d) :
    xL Φ n i ∈ (pI 𝓞 p (Lev Φ n)).radical := by
  obtain ⟨N, hN⟩ := hnil i
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hN
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨N, ?_⟩
  have h0 : πL Φ n a = 0 := (πL_eq_zero_iff Φ n a).2 ha
  have hp : πL Φ n (p : MvPowerSeries (Fin d) 𝓞) = algebraMap 𝓞 (Lev Φ n) (p : 𝓞) := by
    rw [← map_natCast (algebraMap 𝓞 (MvPowerSeries (Fin d) 𝓞)) p, AlgHom.commutes]
  show (πL Φ n (X i)) ^ N ∈ _
  rw [← map_pow, ← hab, map_add, h0, zero_add, map_mul, hp]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in

theorem mem_radical_map {B C : Type*} [CommRing B] [CommRing C] [Algebra 𝓞 B] [Algebra 𝓞 C]
    (u : B →ₐ[𝓞] C) {a : B} (ha : a ∈ (pI 𝓞 p B).radical) : u a ∈ (pI 𝓞 p C).radical := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨k, ?_⟩
  rw [← map_pow, ← hc, map_mul, AlgHom.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
theorem map_pI_mem_radical {B C : Type*} [CommRing B] [CommRing C] [Algebra 𝓞 B] [Algebra 𝓞 C]
    (u : B →ₐ[𝓞] C) : ∀ s ∈ pI 𝓞 p B, u s ∈ (pI 𝓞 p C).radical := by
  intro s hs
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  refine ⟨1, ?_⟩
  rw [pow_one, map_mul, AlgHom.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
theorem pI_fg {B : Type*} [CommRing B] [Algebra 𝓞 B] : (pI 𝓞 p B).FG :=
  ⟨{algebraMap 𝓞 B (p : 𝓞)}, by simp [pI]⟩

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in

theorem algHom_ext_of_xL (hnil : NilHyp p Φ n) {T : Type*} [CommRing T] [Algebra 𝓞 T]
    [IsAdicComplete (pI 𝓞 p T) T] {u w : Lev Φ n →ₐ[𝓞] T}
    (huw : ∀ i, u (xL Φ n i) = w (xL Φ n i)) : u = w := by
  refine AlgHom.ext fun a => ?_
  obtain ⟨G, rfl⟩ := πL_surjective Φ n a
  have hu := algHom_eq_adicEval (pI 𝓞 p T) (u.comp (πL Φ n))
    (fun i => mem_radical_map u (xL_mem_radical hnil i)) G
  have hw := algHom_eq_adicEval (pI 𝓞 p T) (w.comp (πL Φ n))
    (fun i => mem_radical_map w (xL_mem_radical hnil i)) G
  rw [AlgHom.comp_apply] at hu hw
  rw [hu, hw]
  congr 1
  funext i
  exact huw i

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in

theorem algHom_πL_eq_adicEval (hnil : NilHyp p Φ n) {T : Type*} [CommRing T] [Algebra 𝓞 T]
    [IsAdicComplete (pI 𝓞 p T) T] (u : Lev Φ n →ₐ[𝓞] T) (G : MvPowerSeries (Fin d) 𝓞) :
    u (πL Φ n G) = MvFormalGroup.adicEval (pI 𝓞 p T) (fun i => u (xL Φ n i)) G := by
  have hu := algHom_eq_adicEval (pI 𝓞 p T) (u.comp (πL Φ n))
    (fun i => mem_radical_map u (xL_mem_radical hnil i)) G
  rw [AlgHom.comp_apply] at hu
  exact hu

omit [Φ.IsComm] in

theorem πL_eq_adicEval (hnil : NilHyp p Φ n) [Module.Free 𝓞 (Lev Φ n)] [Module.Finite 𝓞 (Lev Φ n)]
    (G : MvPowerSeries (Fin d) 𝓞) :
    πL Φ n G = MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) G := by
  haveI : Fintype (Module.Free.ChooseBasisIndex 𝓞 (Lev Φ n)) := Module.Free.ChooseBasisIndex.fintype 𝓞 (Lev Φ n)
  haveI := isAdicComplete_of_basis 𝓞 p (Lev Φ n) (Module.Free.chooseBasis 𝓞 (Lev Φ n))
  have h := algHom_πL_eq_adicEval hnil (AlgHom.id 𝓞 (Lev Φ n)) G
  exact h

section Structure

variable (hnil : NilHyp p Φ n) [Module.Free 𝓞 (Lev Φ n)] [Module.Finite 𝓞 (Lev Φ n)]

abbrev L2 : Type u := Lev Φ n ⊗[𝓞] Lev Φ n

abbrev L3 : Type u := Lev Φ n ⊗[𝓞] (Lev Φ n ⊗[𝓞] Lev Φ n)

noncomputable def bL : Module.Basis (Module.Free.ChooseBasisIndex 𝓞 (Lev Φ n)) 𝓞 (Lev Φ n) :=
  Module.Free.chooseBasis 𝓞 (Lev Φ n)

noncomputable scoped instance : Fintype (Module.Free.ChooseBasisIndex 𝓞 (Lev Φ n)) :=
  Module.Free.ChooseBasisIndex.fintype 𝓞 (Lev Φ n)

omit [Φ.IsComm] in
theorem complete_L : IsAdicComplete (pI 𝓞 p (Lev Φ n)) (Lev Φ n) :=
  isAdicComplete_of_basis 𝓞 p (Lev Φ n) (bL (Φ := Φ) (n := n))

omit [Φ.IsComm] in
theorem complete_L2 : IsAdicComplete (pI 𝓞 p (L2 (Φ := Φ) (n := n))) (L2 (Φ := Φ) (n := n)) :=
  isAdicComplete_of_basis 𝓞 p (L2 (Φ := Φ) (n := n)) ((bL (Φ := Φ) (n := n)).tensorProduct (bL (Φ := Φ) (n := n)))

noncomputable def yL : Fin d ⊕ Fin d → L2 (Φ := Φ) (n := n) :=
  Sum.elim (fun j => xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n)) (fun j => (1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j)

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)]
  [Module.Finite 𝓞 (Lev Φ n)] in
theorem yL_inl (j : Fin d) : yL (Φ := Φ) (n := n) (Sum.inl j) =
    (Algebra.TensorProduct.includeLeft : Lev Φ n →ₐ[𝓞] L2 (Φ := Φ) (n := n)) (xL Φ n j) := rfl

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)]
  [Module.Finite 𝓞 (Lev Φ n)] in
theorem yL_inr (j : Fin d) : yL (Φ := Φ) (n := n) (Sum.inr j) =
    (Algebra.TensorProduct.includeRight : Lev Φ n →ₐ[𝓞] L2 (Φ := Φ) (n := n)) (xL Φ n j) := rfl

include hnil

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)]
  [Module.Finite 𝓞 (Lev Φ n)] in
theorem yL_mem_radical (s : Fin d ⊕ Fin d) :
    yL (Φ := Φ) (n := n) s ∈ (pI 𝓞 p (L2 (Φ := Φ) (n := n))).radical := by
  rcases s with j | j
  · rw [yL_inl]
    exact mem_radical_map (B := Lev Φ n) (C := L2 (Φ := Φ) (n := n)) Algebra.TensorProduct.includeLeft
      (xL_mem_radical hnil j)
  · rw [yL_inr]
    exact mem_radical_map (B := Lev Φ n) (C := L2 (Φ := Φ) (n := n)) Algebra.TensorProduct.includeRight
      (xL_mem_radical hnil j)

noncomputable def comulSeries : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L2 (Φ := Φ) (n := n) :=
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)
  (MvFormalGroup.adicEvalAlgHom (pI 𝓞 p (L2 (Φ := Φ) (n := n))) (yL_mem_radical hnil)).comp
    (substAlgHom Φ.hasSubst_toPowerSeries)

omit [Φ.IsComm] in
theorem comulSeries_apply (G : MvPowerSeries (Fin d) 𝓞) :
    comulSeries hnil G = MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (subst Φ.toPowerSeries G) := by
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)
  show (MvFormalGroup.adicEvalAlgHom (pI 𝓞 p (L2 (Φ := Φ) (n := n))) (yL_mem_radical hnil))
    (substAlgHom Φ.hasSubst_toPowerSeries G) = _
  rw [MvFormalGroup.coe_adicEvalAlgHom, substAlgHom_apply]

omit [Φ.IsComm] in
theorem comulSeries_X (i : Fin d) :
    comulSeries hnil (X i) = MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (Φ.toPowerSeries i) := by
  rw [comulSeries_apply, subst_X Φ.hasSubst_toPowerSeries]

omit [Φ.IsComm] in

theorem adicEval_yL_inl (G : MvPowerSeries (Fin d) 𝓞) :
    MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) =
      (Algebra.TensorProduct.includeLeft : Lev Φ n →ₐ[𝓞] L2 (Φ := Φ) (n := n)) (πL Φ n G) := by
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)
  have hXl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  rw [MvFormalGroup.adicEval_subst _ (yL_mem_radical hnil) hXl]
  have h := algHom_πL_eq_adicEval hnil (T := L2 (Φ := Φ) (n := n)) Algebra.TensorProduct.includeLeft G
  rw [h]
  congr 1
  funext j
  rw [MvFormalGroup.adicEval_X]
  rfl

omit [Φ.IsComm] in
theorem adicEval_yL_inr (G : MvPowerSeries (Fin d) 𝓞) :
    MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) =
      (Algebra.TensorProduct.includeRight : Lev Φ n →ₐ[𝓞] L2 (Φ := Φ) (n := n)) (πL Φ n G) := by
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)
  have hXr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  rw [MvFormalGroup.adicEval_subst _ (yL_mem_radical hnil) hXr]
  have h := algHom_πL_eq_adicEval hnil (T := L2 (Φ := Φ) (n := n)) Algebra.TensorProduct.includeRight G
  rw [h]
  congr 1
  funext j
  rw [MvFormalGroup.adicEval_X]
  rfl

theorem comulSeries_nthSeries (i : Fin d) : comulSeries hnil (Φ.nthSeries n i) = 0 := by
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)
  rw [comulSeries_apply]
  have hend := (n : MvFormalGroup.End Φ).subst_eq i
  rw [MvFormalGroup.End.toPowerSeries_natCast] at hend
  rw [hend]
  have hu : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
      (Φ.nthSeries n j)).constantCoeff = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
      (fun l => constantCoeff_X _) (MvFormalGroup.constantCoeff_nthSeries Φ n j)
  have hv : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
      (Φ.nthSeries n j)).constantCoeff = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
      (fun l => constantCoeff_X _) (MvFormalGroup.constantCoeff_nthSeries Φ n j)
  rw [MvFormalGroup.adicEval_subst_elim Φ _ (yL_mem_radical hnil) hu hv]
  have h0 : ∀ j, πL Φ n (Φ.nthSeries n j) = 0 := fun j =>
    (πL_eq_zero_iff Φ n _).2 (Ideal.subset_span ⟨j, rfl⟩)
  have hl : (fun j => MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (Φ.nthSeries n j))) =
      fun _ => 0 := by
    funext j; rw [adicEval_yL_inl hnil, h0, map_zero]
  have hr : (fun j => MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (Φ.nthSeries n j))) =
      fun _ => 0 := by
    funext j; rw [adicEval_yL_inr hnil, h0, map_zero]
  rw [hl, hr]

  have hz0 : MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (0 : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) = 0 := by
    rw [← MvFormalGroup.coe_adicEvalAlgHom _ (yL_mem_radical hnil), map_zero]
  have hz : (Sum.elim (fun _ : Fin d => (0 : L2 (Φ := Φ) (n := n))) fun _ : Fin d => (0 : L2 (Φ := Φ) (n := n))) =
      fun s => MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
        ((fun _ : Fin d ⊕ Fin d => (0 : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) s) := by
    funext s
    rcases s with j | j
    · exact hz0.symm
    · exact hz0.symm
  rw [hz, ← MvFormalGroup.adicEval_subst _ (yL_mem_radical hnil)
    (hasSubst_of_constantCoeff_zero fun _ => map_zero _),
    MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (Φ.constantCoeff_eq_zero i), hz0]

noncomputable def comulL : Lev Φ n →ₐ[𝓞] L2 (Φ := Φ) (n := n) :=
  Ideal.Quotient.liftₐ _ (comulSeries hnil) (by
    show Ideal.span (Set.range (Φ.nthSeries n)) ≤ RingHom.ker (comulSeries hnil)
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact comulSeries_nthSeries hnil i)

theorem comulL_πL (G : MvPowerSeries (Fin d) 𝓞) : comulL hnil (πL Φ n G) = comulSeries hnil G := rfl

theorem comulL_xL (i : Fin d) :
    comulL hnil (xL Φ n i) = MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (Φ.toPowerSeries i) := by
  rw [← πL_X, comulL_πL, comulSeries_X]

omit hnil

noncomputable def constantCoeffAlg : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 :=
  { (constantCoeff : MvPowerSeries (Fin d) 𝓞 →+* 𝓞) with
    commutes' := fun r => by
      show constantCoeff (algebraMap 𝓞 (MvPowerSeries (Fin d) 𝓞) r) = r
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C] }

noncomputable def counitL : Lev Φ n →ₐ[𝓞] 𝓞 :=
  Ideal.Quotient.liftₐ (Ideal.span (Set.range (Φ.nthSeries n))) constantCoeffAlg (by
    show Ideal.span (Set.range (Φ.nthSeries n)) ≤ RingHom.ker _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact MvFormalGroup.constantCoeff_nthSeries Φ n i)

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)]
  [Module.Finite 𝓞 (Lev Φ n)] in
theorem counitL_πL (G : MvPowerSeries (Fin d) 𝓞) : counitL (Φ := Φ) (n := n) (πL Φ n G) = constantCoeff G := rfl

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)]
  [Module.Finite 𝓞 (Lev Φ n)] in
theorem counitL_xL (i : Fin d) : counitL (Φ := Φ) (n := n) (xL Φ n i) = 0 := by
  rw [← πL_X, counitL_πL, constantCoeff_X]

include hnil

theorem map_comulL_xL {T : Type*} [CommRing T] [Algebra 𝓞 T] [IsAdicComplete (pI 𝓞 p T) T]
    (w : L2 (Φ := Φ) (n := n) →ₐ[𝓞] T) (i : Fin d) :
    w (comulL hnil (xL Φ n i)) = MvFormalGroup.adicEval (pI 𝓞 p T)
      (Sum.elim (fun j => w (xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n))) (fun j => w ((1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j)))
      (Φ.toPowerSeries i) := by
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)
  rw [comulL_xL, MvFormalGroup.map_adicEval _ (pI 𝓞 p T) w pI_fg
    (map_pI_mem_radical (B := L2 (Φ := Φ) (n := n)) (C := T) w) (yL_mem_radical hnil)]
  congr 1
  funext s
  rcases s with j | j <;> rfl

omit hnil [Module.Free 𝓞 (Lev Φ n)] [Module.Finite 𝓞 (Lev Φ n)] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  [Φ.IsComm] in

theorem adicEval_elim_zero_left {T : Type*} [CommRing T] [Algebra 𝓞 T]
    [IsAdicComplete (pI 𝓞 p T) T] {t : Fin d → T}
    (ht : ∀ j, t j ∈ (pI 𝓞 p T).radical) (i : Fin d) :
    MvFormalGroup.adicEval (pI 𝓞 p T) (Sum.elim (fun _ : Fin d => (0 : T)) t) (Φ.toPowerSeries i) = t i := by
  have hfam : Sum.elim (fun _ : Fin d => (0 : T)) t = fun s => MvFormalGroup.adicEval (pI 𝓞 p T) t
      ((Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) 𝓞)) fun j => X j) s) := by
    funext s
    rcases s with j | j
    · show (0 : T) = MvFormalGroup.adicEval _ t (0 : MvPowerSeries (Fin d) 𝓞)
      rw [← MvFormalGroup.coe_adicEvalAlgHom _ ht, map_zero]
    · show t j = MvFormalGroup.adicEval _ t (X j : MvPowerSeries (Fin d) 𝓞)
      rw [MvFormalGroup.adicEval_X]
  rw [hfam, ← MvFormalGroup.adicEval_subst _ ht (MvFormalGroup.hasSubst_elim (fun _ => map_zero _)
    (fun j => constantCoeff_X j)), MvFormalGroup.subst_elim_zero_X Φ i, MvFormalGroup.adicEval_X]

omit hnil [Module.Free 𝓞 (Lev Φ n)] [Module.Finite 𝓞 (Lev Φ n)] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  [Φ.IsComm] in

theorem adicEval_elim_zero_right {T : Type*} [CommRing T] [Algebra 𝓞 T]
    [IsAdicComplete (pI 𝓞 p T) T] {t : Fin d → T}
    (ht : ∀ j, t j ∈ (pI 𝓞 p T).radical) (i : Fin d) :
    MvFormalGroup.adicEval (pI 𝓞 p T) (Sum.elim t fun _ : Fin d => (0 : T)) (Φ.toPowerSeries i) = t i := by
  have hfam : (Sum.elim t fun _ : Fin d => (0 : T)) = fun s => MvFormalGroup.adicEval (pI 𝓞 p T) t
      ((Sum.elim (fun j => (X j : MvPowerSeries (Fin d) 𝓞)) fun _ : Fin d => 0) s) := by
    funext s
    rcases s with j | j
    · show t j = MvFormalGroup.adicEval _ t (X j : MvPowerSeries (Fin d) 𝓞)
      rw [MvFormalGroup.adicEval_X]
    · show (0 : T) = MvFormalGroup.adicEval _ t (0 : MvPowerSeries (Fin d) 𝓞)
      rw [← MvFormalGroup.coe_adicEvalAlgHom _ ht, map_zero]
  rw [hfam, ← MvFormalGroup.adicEval_subst _ ht (MvFormalGroup.hasSubst_elim (fun j => constantCoeff_X j)
    (fun _ => map_zero _)), MvFormalGroup.subst_elim_X_zero Φ i, MvFormalGroup.adicEval_X]

theorem coassoc :
    (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulL hnil) (.id 𝓞 (Lev Φ n))).comp (comulL hnil))
      = (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (comulL hnil)).comp (comulL hnil) := by
  letI iCR : CommRing (L3 (Φ := Φ) (n := n)) := Algebra.TensorProduct.instCommRing
  letI iAlg : Algebra 𝓞 (L3 (Φ := Φ) (n := n)) := Algebra.TensorProduct.leftAlgebra
  haveI : IsAdicComplete (pI 𝓞 p (L3 (Φ := Φ) (n := n))) (L3 (Φ := Φ) (n := n)) :=
    isAdicComplete_of_basis 𝓞 p (L3 (Φ := Φ) (n := n))
      ((bL (Φ := Φ) (n := n)).tensorProduct ((bL (Φ := Φ) (n := n)).tensorProduct (bL (Φ := Φ) (n := n))))
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)

  let ea : Lev Φ n →ₐ[𝓞] L3 (Φ := Φ) (n := n) := Algebra.TensorProduct.includeLeft
  let eb : Lev Φ n →ₐ[𝓞] L3 (Φ := Φ) (n := n) :=
    (Algebra.TensorProduct.includeRight : L2 (Φ := Φ) (n := n) →ₐ[𝓞] L3 (Φ := Φ) (n := n)).comp
      (Algebra.TensorProduct.includeLeft : Lev Φ n →ₐ[𝓞] L2 (Φ := Φ) (n := n))
  let ec : Lev Φ n →ₐ[𝓞] L3 (Φ := Φ) (n := n) :=
    (Algebra.TensorProduct.includeRight : L2 (Φ := Φ) (n := n) →ₐ[𝓞] L3 (Φ := Φ) (n := n)).comp
      (Algebra.TensorProduct.includeRight : Lev Φ n →ₐ[𝓞] L2 (Φ := Φ) (n := n))
  let a : Fin d → L3 (Φ := Φ) (n := n) := fun j => ea (xL Φ n j)
  let b : Fin d → L3 (Φ := Φ) (n := n) := fun j => eb (xL Φ n j)
  let c : Fin d → L3 (Φ := Φ) (n := n) := fun j => ec (xL Φ n j)
  have har : ∀ j, a j ∈ (pI 𝓞 p (L3 (Φ := Φ) (n := n))).radical := fun j =>
    mem_radical_map (B := Lev Φ n) (C := L3 (Φ := Φ) (n := n)) ea (xL_mem_radical hnil j)
  have hbr : ∀ j, b j ∈ (pI 𝓞 p (L3 (Φ := Φ) (n := n))).radical := fun j =>
    mem_radical_map (B := Lev Φ n) (C := L3 (Φ := Φ) (n := n)) eb (xL_mem_radical hnil j)
  have hcr : ∀ j, c j ∈ (pI 𝓞 p (L3 (Φ := Φ) (n := n))).radical := fun j =>
    mem_radical_map (B := Lev Φ n) (C := L3 (Φ := Φ) (n := n)) ec (xL_mem_radical hnil j)
  let z : Fin d ⊕ (Fin d ⊕ Fin d) → L3 (Φ := Φ) (n := n) := Sum.elim a (Sum.elim b c)
  have hzr : ∀ s, z s ∈ (pI 𝓞 p (L3 (Φ := Φ) (n := n))).radical := by
    rintro (j | j | j)
    exacts [har j, hbr j, hcr j]
  have habr : ∀ s, Sum.elim a b s ∈ (pI 𝓞 p (L3 (Φ := Φ) (n := n))).radical := by
    rintro (j | j)
    exacts [har j, hbr j]
  have hbcr : ∀ s, Sum.elim b c s ∈ (pI 𝓞 p (L3 (Φ := Φ) (n := n))).radical := by
    rintro (j | j)
    exacts [hbr j, hcr j]
  refine algHom_ext_of_xL hnil (T := L3 (Φ := Φ) (n := n)) fun i => ?_

  set wL : L2 (Φ := Φ) (n := n) →ₐ[𝓞] L3 (Φ := Φ) (n := n) :=
    (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n)).toAlgHom.comp
      (Algebra.TensorProduct.map (comulL hnil) (.id 𝓞 (Lev Φ n))) with hwL
  have hL : wL (comulL hnil (xL Φ n i)) = MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z
        (subst (Sum.elim (fun j => subst (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
            fun l => X (Sum.inr (Sum.inl l))) (Φ.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j))) (Φ.toPowerSeries i)) := by
    rw [map_comulL_xL hnil (T := L3 (Φ := Φ) (n := n))]
    have hB : ∀ s : Fin d ⊕ Fin d, ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
        fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hu : ∀ j, (subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
        fun l => X (Sum.inr (Sum.inl l))) (Φ.toPowerSeries j)).constantCoeff = 0 := fun j =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hB) hB (Φ.constantCoeff_eq_zero j)
    have hv : ∀ j, (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞).constantCoeff = 0 :=
      fun j => constantCoeff_X _
    rw [MvFormalGroup.adicEval_subst_elim Φ _ hzr hu hv]
    congr 1
    funext s
    rcases s with j | j
    ·
      have h1 : wL (xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n)) =
          ((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n)).toAlgHom.comp
            (Algebra.TensorProduct.includeLeft : L2 (Φ := Φ) (n := n) →ₐ[𝓞] _)) (comulL hnil (xL Φ n j)) := by
        show (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n)).toAlgHom
            ((Algebra.TensorProduct.map (comulL hnil) (.id 𝓞 (Lev Φ n))) (xL Φ n j ⊗ₜ[𝓞] 1)) = _
        rw [Algebra.TensorProduct.map_tmul]
        rfl
      show wL (xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n)) = MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z
        (subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
          fun l => X (Sum.inr (Sum.inl l))) (Φ.toPowerSeries j))
      have hXa : ∀ l, (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞).constantCoeff = 0 :=
        fun l => constantCoeff_X _
      have hXb : ∀ l, (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞).constantCoeff = 0 :=
        fun l => constantCoeff_X _
      rw [h1, map_comulL_xL hnil (T := L3 (Φ := Φ) (n := n)),
        MvFormalGroup.adicEval_subst_elim Φ _ hzr hXa hXb]
      congr 1
      funext s'
      rcases s' with l | l
      · show ((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n)).toAlgHom.comp
            Algebra.TensorProduct.includeLeft) (xL Φ n l ⊗ₜ[𝓞] 1) =
            MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z (X (Sum.inl l))
        rw [MvFormalGroup.adicEval_X]
        show (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n))
            ((xL Φ n l ⊗ₜ[𝓞] (1 : Lev Φ n)) ⊗ₜ[𝓞] (1 : Lev Φ n)) = a l
        rw [Algebra.TensorProduct.assoc_tmul]
        rfl
      · show ((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n)).toAlgHom.comp
            Algebra.TensorProduct.includeLeft) ((1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n l) =
            MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z (X (Sum.inr (Sum.inl l)))
        rw [MvFormalGroup.adicEval_X]
        show (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n))
            (((1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n l) ⊗ₜ[𝓞] (1 : Lev Φ n)) = b l
        rw [Algebra.TensorProduct.assoc_tmul]
        rfl
    · show wL ((1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j) =
          MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z (X (Sum.inr (Sum.inr j)))
      rw [MvFormalGroup.adicEval_X]
      show (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n)).toAlgHom
          ((Algebra.TensorProduct.map (comulL hnil) (.id 𝓞 (Lev Φ n))) (1 ⊗ₜ[𝓞] xL Φ n j)) = c j
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      show (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 (Lev Φ n) (Lev Φ n) (Lev Φ n))
          (((1 : Lev Φ n) ⊗ₜ[𝓞] (1 : Lev Φ n)) ⊗ₜ[𝓞] xL Φ n j) = c j
      rw [Algebra.TensorProduct.assoc_tmul]
      rfl

  set wR : L2 (Φ := Φ) (n := n) →ₐ[𝓞] L3 (Φ := Φ) (n := n) :=
    Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (comulL hnil) with hwR
  have hR : wR (comulL hnil (xL Φ n i)) = MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z
        (subst (Sum.elim (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
          fun j => subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
            fun l => X (Sum.inr (Sum.inr l))) (Φ.toPowerSeries j)) (Φ.toPowerSeries i)) := by
    rw [map_comulL_xL hnil (T := L3 (Φ := Φ) (n := n))]
    have hC : ∀ s : Fin d ⊕ Fin d, ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
        fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hu : ∀ j, (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞).constantCoeff = 0 :=
      fun j => constantCoeff_X _
    have hv : ∀ j, (subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
        fun l => X (Sum.inr (Sum.inr l))) (Φ.toPowerSeries j)).constantCoeff = 0 := fun j =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hC) hC (Φ.constantCoeff_eq_zero j)
    rw [MvFormalGroup.adicEval_subst_elim Φ _ hzr hu hv]
    congr 1
    funext s
    rcases s with j | j
    · show wR (xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n)) =
          MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z (X (Sum.inl j))
      rw [MvFormalGroup.adicEval_X]
      show (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (comulL hnil)) (xL Φ n j ⊗ₜ[𝓞] 1) = a j
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      rfl
    · have h1 : wR ((1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j) =
          (Algebra.TensorProduct.includeRight : L2 (Φ := Φ) (n := n) →ₐ[𝓞] L3 (Φ := Φ) (n := n))
            (comulL hnil (xL Φ n j)) := by
        show (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (comulL hnil)) (1 ⊗ₜ[𝓞] xL Φ n j) = _
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        rfl
      show wR ((1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j) = MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z
        (subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
          fun l => X (Sum.inr (Sum.inr l))) (Φ.toPowerSeries j))
      have hXb : ∀ l, (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞).constantCoeff = 0 :=
        fun l => constantCoeff_X _
      have hXc : ∀ l, (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞).constantCoeff = 0 :=
        fun l => constantCoeff_X _
      rw [h1, map_comulL_xL hnil (T := L3 (Φ := Φ) (n := n)),
        MvFormalGroup.adicEval_subst_elim Φ _ hzr hXb hXc]
      congr 1
      funext s'
      rcases s' with l | l
      · show (Algebra.TensorProduct.includeRight : L2 (Φ := Φ) (n := n) →ₐ[𝓞] L3 (Φ := Φ) (n := n))
            (xL Φ n l ⊗ₜ[𝓞] 1) = MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z (X (Sum.inr (Sum.inl l)))
        rw [MvFormalGroup.adicEval_X]
        rfl
      · show (Algebra.TensorProduct.includeRight : L2 (Φ := Φ) (n := n) →ₐ[𝓞] L3 (Φ := Φ) (n := n))
            (1 ⊗ₜ[𝓞] xL Φ n l) = MvFormalGroup.adicEval (pI 𝓞 p (L3 (Φ := Φ) (n := n))) z (X (Sum.inr (Sum.inr l)))
        rw [MvFormalGroup.adicEval_X]
        rfl
  show wL (comulL hnil (xL Φ n i)) = wR (comulL hnil (xL Φ n i))
  rw [hL, hR, Φ.assoc i]

theorem rTensor_counit :
    (Algebra.TensorProduct.map (counitL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))).comp (comulL hnil)
      = (Algebra.TensorProduct.lid 𝓞 (Lev Φ n)).symm := by
  haveI : IsAdicComplete (pI 𝓞 p (𝓞 ⊗[𝓞] Lev Φ n)) (𝓞 ⊗[𝓞] Lev Φ n) :=
    isAdicComplete_of_basis 𝓞 p (𝓞 ⊗[𝓞] Lev Φ n)
      ((Module.Basis.singleton Unit 𝓞).tensorProduct (bL (Φ := Φ) (n := n)))
  refine algHom_ext_of_xL hnil (T := 𝓞 ⊗[𝓞] Lev Φ n) fun i => ?_
  rw [AlgHom.comp_apply, map_comulL_xL hnil (T := 𝓞 ⊗[𝓞] Lev Φ n)]
  have ht : ∀ j, (Algebra.TensorProduct.includeRight : Lev Φ n →ₐ[𝓞] 𝓞 ⊗[𝓞] Lev Φ n) (xL Φ n j) ∈
      (pI 𝓞 p (𝓞 ⊗[𝓞] Lev Φ n)).radical := fun j =>
    mem_radical_map (B := Lev Φ n) (C := 𝓞 ⊗[𝓞] Lev Φ n) Algebra.TensorProduct.includeRight (xL_mem_radical hnil j)
  have hfam : (Sum.elim (fun j => (Algebra.TensorProduct.map (counitL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))) (xL Φ n j ⊗ₜ[𝓞] 1))
      fun j => (Algebra.TensorProduct.map (counitL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))) (1 ⊗ₜ[𝓞] xL Φ n j)) =
      Sum.elim (fun _ : Fin d => (0 : 𝓞 ⊗[𝓞] Lev Φ n)) fun j =>
        (Algebra.TensorProduct.includeRight : Lev Φ n →ₐ[𝓞] 𝓞 ⊗[𝓞] Lev Φ n) (xL Φ n j) := by
    funext s
    rcases s with j | j
    · show (Algebra.TensorProduct.map (counitL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))) (xL Φ n j ⊗ₜ[𝓞] 1) = 0
      rw [Algebra.TensorProduct.map_tmul, counitL_xL, TensorProduct.zero_tmul]
    · show (Algebra.TensorProduct.map (counitL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))) (1 ⊗ₜ[𝓞] xL Φ n j) = _
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      rfl
  rw [hfam, adicEval_elim_zero_left (T := 𝓞 ⊗[𝓞] Lev Φ n) ht]
  rfl

theorem lTensor_counit :
    (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (counitL (Φ := Φ) (n := n))).comp (comulL hnil)
      = (Algebra.TensorProduct.rid 𝓞 𝓞 (Lev Φ n)).symm := by
  haveI : IsAdicComplete (pI 𝓞 p (Lev Φ n ⊗[𝓞] 𝓞)) (Lev Φ n ⊗[𝓞] 𝓞) :=
    isAdicComplete_of_basis 𝓞 p (Lev Φ n ⊗[𝓞] 𝓞)
      ((bL (Φ := Φ) (n := n)).tensorProduct (Module.Basis.singleton Unit 𝓞))
  refine algHom_ext_of_xL hnil (T := Lev Φ n ⊗[𝓞] 𝓞) fun i => ?_
  rw [AlgHom.comp_apply, map_comulL_xL hnil (T := Lev Φ n ⊗[𝓞] 𝓞)]
  have ht : ∀ j, (Algebra.TensorProduct.includeLeft : Lev Φ n →ₐ[𝓞] Lev Φ n ⊗[𝓞] 𝓞) (xL Φ n j) ∈
      (pI 𝓞 p (Lev Φ n ⊗[𝓞] 𝓞)).radical := fun j =>
    mem_radical_map (B := Lev Φ n) (C := Lev Φ n ⊗[𝓞] 𝓞) Algebra.TensorProduct.includeLeft (xL_mem_radical hnil j)
  have hfam : (Sum.elim (fun j => (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (counitL (Φ := Φ) (n := n))) (xL Φ n j ⊗ₜ[𝓞] 1))
      fun j => (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (counitL (Φ := Φ) (n := n))) (1 ⊗ₜ[𝓞] xL Φ n j)) =
      Sum.elim (fun j => (Algebra.TensorProduct.includeLeft : Lev Φ n →ₐ[𝓞] Lev Φ n ⊗[𝓞] 𝓞) (xL Φ n j))
        fun _ : Fin d => (0 : Lev Φ n ⊗[𝓞] 𝓞) := by
    funext s
    rcases s with j | j
    · show (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (counitL (Φ := Φ) (n := n))) (xL Φ n j ⊗ₜ[𝓞] 1) = _
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      rfl
    · show (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (counitL (Φ := Φ) (n := n))) (1 ⊗ₜ[𝓞] xL Φ n j) = 0
      rw [Algebra.TensorProduct.map_tmul, counitL_xL, TensorProduct.tmul_zero]
  rw [hfam, adicEval_elim_zero_right (T := Lev Φ n ⊗[𝓞] 𝓞) ht]
  rfl

@[reducible] noncomputable def bialg : Bialgebra 𝓞 (Lev Φ n) :=
  Bialgebra.ofAlgHom (comulL hnil) counitL (coassoc hnil) (rTensor_counit hnil) (lTensor_counit hnil)

omit hnil

noncomputable def antipodeSeries : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] Lev Φ n :=
  (πL Φ n).comp (substAlgHom (MvFormalGroup.hasSubst_invSeries Φ))

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)]
  [Module.Finite 𝓞 (Lev Φ n)] in
theorem antipodeSeries_apply (G : MvPowerSeries (Fin d) 𝓞) :
    antipodeSeries (Φ := Φ) (n := n) G = πL Φ n (subst (MvFormalGroup.invSeries Φ) G) := by
  rw [antipodeSeries, AlgHom.comp_apply, substAlgHom_apply]

omit [Φ.IsComm] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)]
  [Module.Finite 𝓞 (Lev Φ n)] in

theorem subst_mem_span {τ : Type*} {g : Fin d → MvPowerSeries τ 𝓞} (hg : HasSubst g)
    {G : MvPowerSeries (Fin d) 𝓞} (hG : constantCoeff G = 0) : subst g G ∈ Ideal.span (Set.range g) := by
  have hmem : G ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) := by
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff]; exact hG
  have := Ideal.mem_map_of_mem (substAlgHom (R := 𝓞) hg) hmem
  rw [Ideal.map_span] at this
  rw [← substAlgHom_apply hg]
  refine Ideal.span_mono ?_ this
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, by rw [substAlgHom_apply, subst_X hg]⟩

omit [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)] [Module.Finite 𝓞 (Lev Φ n)] in

theorem antipodeSeries_nthSeries (i : Fin d) : antipodeSeries (Φ := Φ) (n := n) (Φ.nthSeries n i) = 0 := by
  rw [antipodeSeries_apply]
  have hcomm : ((n : MvFormalGroup.End Φ) * (-1 : MvFormalGroup.End Φ)) =
      (-1 : MvFormalGroup.End Φ) * (n : MvFormalGroup.End Φ) :=
    (Nat.cast_commute n (-1 : MvFormalGroup.End Φ)).eq
  have h := congrArg (fun φ : MvFormalGroup.End Φ => MvFormalGroup.Hom.toPowerSeries φ i) hcomm
  simp only [MvFormalGroup.End.toPowerSeries_mul, MvFormalGroup.End.toPowerSeries_natCast,
    MvFormalGroup.End.toPowerSeries_neg_one] at h
  rw [h]
  exact (πL_eq_zero_iff Φ n _).2 (subst_mem_span
    (hasSubst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries Φ n))
    (MvFormalGroup.constantCoeff_invSeries Φ i))

noncomputable def antipodeL : Lev Φ n →ₐ[𝓞] Lev Φ n :=
  Ideal.Quotient.liftₐ (Ideal.span (Set.range (Φ.nthSeries n))) antipodeSeries (by
    show Ideal.span (Set.range (Φ.nthSeries n)) ≤ RingHom.ker _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact antipodeSeries_nthSeries i)

omit [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [Module.Free 𝓞 (Lev Φ n)] [Module.Finite 𝓞 (Lev Φ n)] in
theorem antipodeL_πL (G : MvPowerSeries (Fin d) 𝓞) :
    antipodeL (Φ := Φ) (n := n) (πL Φ n G) = πL Φ n (subst (MvFormalGroup.invSeries Φ) G) :=
  antipodeSeries_apply G

include hnil

theorem antipodeL_xL (i : Fin d) :
    antipodeL (Φ := Φ) (n := n) (xL Φ n i) =
      MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) (MvFormalGroup.invSeries Φ i) := by
  rw [← πL_X, antipodeL_πL, subst_X (MvFormalGroup.hasSubst_invSeries Φ), πL_eq_adicEval hnil]

theorem antipode_right :
    (Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
      ((Algebra.TensorProduct.map (antipodeL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))).comp (comulL hnil)) =
      (Algebra.ofId 𝓞 (Lev Φ n)).comp counitL := by
  haveI := complete_L (p := p) (Φ := Φ) (n := n)
  refine algHom_ext_of_xL hnil (T := Lev Φ n) fun i => ?_
  have hR : ((Algebra.ofId 𝓞 (Lev Φ n)).comp counitL) (xL Φ n i) = 0 := by
    rw [AlgHom.comp_apply, counitL_xL, map_zero]
  rw [hR]
  change ((Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
    (Algebra.TensorProduct.map (antipodeL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n)))) (comulL hnil (xL Φ n i)) = 0
  rw [map_comulL_xL hnil (T := Lev Φ n)]
  have hfam : (Sum.elim
      (fun j => ((Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
        (Algebra.TensorProduct.map (antipodeL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n)))) (xL Φ n j ⊗ₜ[𝓞] 1))
      fun j => ((Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
        (Algebra.TensorProduct.map (antipodeL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n)))) (1 ⊗ₜ[𝓞] xL Φ n j)) =
      Sum.elim (fun j => MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n)
        (MvFormalGroup.invSeries Φ j))
      fun j => MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) (X j : MvPowerSeries (Fin d) 𝓞) := by
    funext s
    rcases s with j | j
    · show (Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n))
          ((Algebra.TensorProduct.map (antipodeL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))) (xL Φ n j ⊗ₜ[𝓞] 1)) =
          MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) (MvFormalGroup.invSeries Φ j)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one,
        antipodeL_xL hnil]
    · show (Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n))
          ((Algebra.TensorProduct.map (antipodeL (Φ := Φ) (n := n)) (.id 𝓞 (Lev Φ n))) (1 ⊗ₜ[𝓞] xL Φ n j)) =
          MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) (X j : MvPowerSeries (Fin d) 𝓞)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul,
        AlgHom.id_apply, MvFormalGroup.adicEval_X]
  rw [hfam, ← MvFormalGroup.adicEval_subst_elim Φ _ (xL_mem_radical hnil) (MvFormalGroup.constantCoeff_invSeries Φ)
    (fun j => constantCoeff_X j), MvFormalGroup.subst_elim_invSeries_X Φ i,
    ← MvFormalGroup.coe_adicEvalAlgHom _ (xL_mem_radical hnil), map_zero]

theorem antipode_left :
    (Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
      ((Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (antipodeL (Φ := Φ) (n := n))).comp (comulL hnil)) =
      (Algebra.ofId 𝓞 (Lev Φ n)).comp counitL := by
  haveI := complete_L (p := p) (Φ := Φ) (n := n)
  refine algHom_ext_of_xL hnil (T := Lev Φ n) fun i => ?_
  have hR : ((Algebra.ofId 𝓞 (Lev Φ n)).comp counitL) (xL Φ n i) = 0 := by
    rw [AlgHom.comp_apply, counitL_xL, map_zero]
  rw [hR]
  change ((Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
    (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (antipodeL (Φ := Φ) (n := n)))) (comulL hnil (xL Φ n i)) = 0
  rw [map_comulL_xL hnil (T := Lev Φ n)]
  have hfam : (Sum.elim
      (fun j => ((Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
        (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (antipodeL (Φ := Φ) (n := n)))) (xL Φ n j ⊗ₜ[𝓞] 1))
      fun j => ((Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n)).comp
        (Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (antipodeL (Φ := Φ) (n := n)))) (1 ⊗ₜ[𝓞] xL Φ n j)) =
      Sum.elim (fun j => MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) (X j : MvPowerSeries (Fin d) 𝓞))
      fun j => MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n)
        (MvFormalGroup.invSeries Φ j) := by
    funext s
    rcases s with j | j
    · show (Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n))
          ((Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (antipodeL (Φ := Φ) (n := n))) (xL Φ n j ⊗ₜ[𝓞] 1)) =
          MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) (X j : MvPowerSeries (Fin d) 𝓞)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one,
        AlgHom.id_apply, MvFormalGroup.adicEval_X]
    · show (Algebra.TensorProduct.lmul' 𝓞 (S := Lev Φ n))
          ((Algebra.TensorProduct.map (.id 𝓞 (Lev Φ n)) (antipodeL (Φ := Φ) (n := n))) (1 ⊗ₜ[𝓞] xL Φ n j)) =
          MvFormalGroup.adicEval (pI 𝓞 p (Lev Φ n)) (xL Φ n) (MvFormalGroup.invSeries Φ j)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul,
        antipodeL_xL hnil]
  rw [hfam, ← MvFormalGroup.adicEval_subst_elim Φ _ (xL_mem_radical hnil) (fun j => constantCoeff_X j)
    (MvFormalGroup.constantCoeff_invSeries Φ), MvFormalGroup.subst_elim_X_invSeries Φ i,
    ← MvFormalGroup.coe_adicEvalAlgHom _ (xL_mem_radical hnil), map_zero]

@[reducible] noncomputable def hopf : HopfAlgebra 𝓞 (Lev Φ n) :=
  letI : Bialgebra 𝓞 (Lev Φ n) := bialg hnil
  { antipode := (antipodeL (Φ := Φ) (n := n)).toLinearMap
    mul_antipode_rTensor_comul := LinearMap.ext fun a => DFunLike.congr_fun (antipode_right hnil) a
    mul_antipode_lTensor_comul := LinearMap.ext fun a => DFunLike.congr_fun (antipode_left hnil) a }

end Structure
p2m_reactivate "P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.P2mTorsionHopf.Lev"

end Level
p2m_reactivate "P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.P2mTorsionHopf.Lev"

section Cocomm

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  {d : ℕ} {Φ : MvFormalGroup d 𝓞} [Φ.IsComm] {n : ℕ}
  (hnil : NilHyp p Φ n) [Module.Free 𝓞 (Lev Φ n)] [Module.Finite 𝓞 (Lev Φ n)]

include hnil

theorem comm_comp_comulL :
    (Algebra.TensorProduct.comm 𝓞 (Lev Φ n) (Lev Φ n)).toAlgHom.comp (comulL hnil) = comulL hnil := by
  haveI := complete_L2 (p := p) (Φ := Φ) (n := n)
  refine algHom_ext_of_xL hnil (T := L2 (Φ := Φ) (n := n)) fun i => ?_
  rw [AlgHom.comp_apply, map_comulL_xL hnil (T := L2 (Φ := Φ) (n := n)), comulL_xL hnil]
  have hfam : (Sum.elim
      (fun j => (Algebra.TensorProduct.comm 𝓞 (Lev Φ n) (Lev Φ n)).toAlgHom (xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n)))
      fun j => (Algebra.TensorProduct.comm 𝓞 (Lev Φ n) (Lev Φ n)).toAlgHom ((1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j)) =
      Sum.elim (fun j => (1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j) fun j => xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n) := by
    funext s
    rcases s with j | j
    · show (Algebra.TensorProduct.comm 𝓞 (Lev Φ n) (Lev Φ n)) (xL Φ n j ⊗ₜ[𝓞] 1) = (1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j
      rw [Algebra.TensorProduct.comm_tmul]
    · show (Algebra.TensorProduct.comm 𝓞 (Lev Φ n) (Lev Φ n)) (1 ⊗ₜ[𝓞] xL Φ n j) = xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n)
      rw [Algebra.TensorProduct.comm_tmul]
  rw [hfam]

  have ha : ∀ j, (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hb : ∀ j, (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hxa : (fun j => MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) = fun j => xL Φ n j ⊗ₜ[𝓞] (1 : Lev Φ n) :=
    funext fun j => MvFormalGroup.adicEval_X _ _ _
  have hyb : (fun j => MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL
      (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) = fun j => (1 : Lev Φ n) ⊗ₜ[𝓞] xL Φ n j :=
    funext fun j => MvFormalGroup.adicEval_X _ _ _
  have key := congrArg (MvFormalGroup.adicEval (pI 𝓞 p (L2 (Φ := Φ) (n := n))) yL)
    (MvFormalGroup.subst_elim_comm Φ ha hb i)
  rw [MvFormalGroup.adicEval_subst_elim Φ _ (yL_mem_radical hnil) ha hb,
    MvFormalGroup.adicEval_subst_elim Φ _ (yL_mem_radical hnil) hb ha, hxa, hyb] at key

  exact key.symm

theorem isCocomm : letI : HopfAlgebra 𝓞 (Lev Φ n) := hopf hnil; Coalgebra.IsCocomm 𝓞 (Lev Φ n) := by
  letI : HopfAlgebra 𝓞 (Lev Φ n) := hopf hnil
  refine ⟨LinearMap.ext fun a => ?_⟩
  exact DFunLike.congr_fun (comm_comp_comulL hnil) a

end Cocomm
p2m_reactivate "P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.P2mTorsionHopf.Lev"

end P2mTorsionHopf
p2m_reactivate "P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.P2mTorsionHopf.Lev P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete.P2mTorsionHopf"

open P2mTorsionHopf in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (n : ℕ)
    [Module.Free 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    [Module.Finite 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n)))]
    (hnil : ∀ i : Fin d, ∃ N : ℕ, (MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞) ^ N ∈
      Ideal.span (Set.range (Φ.nthSeries n)) ⊔ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)}) :
    ∃ (L : Type u) (_ : CommRing L) (_ : HopfAlgebra 𝓞 L) (_ : Coalgebra.IsCocomm 𝓞 L)
      (_ : Module.Free 𝓞 L) (_ : Module.Finite 𝓞 L) (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L),
      Function.Surjective π ∧
      RingHom.ker π = Ideal.span (Set.range (Φ.nthSeries n)) ∧
      (∀ i, π (MvPowerSeries.X i) ∈ (Ideal.span {(p : L)}).radical) ∧
      (∀ G, π G = MvFormalGroup.adicEval (Ideal.span {(p : L)}) (fun i => π (MvPowerSeries.X i)) G) ∧
      (∀ i, Coalgebra.comul (R := 𝓞) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[𝓞] (1 : L))
            (fun j => (1 : L) ⊗ₜ[𝓞] π (MvPowerSeries.X j)))
          (Φ.toPowerSeries i)) ∧
      (∀ G, Coalgebra.counit (R := 𝓞) (π G) = MvPowerSeries.constantCoeff G) := by
  haveI hF : Module.Free 𝓞 (Lev Φ n) :=
    ‹Module.Free 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n)))›
  haveI hFin : Module.Finite 𝓞 (Lev Φ n) :=
    ‹Module.Finite 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (Φ.nthSeries n)))›
  have hnil' : NilHyp p Φ n := hnil
  letI hH : HopfAlgebra 𝓞 (Lev Φ n) := hopf hnil'
  haveI hC : Coalgebra.IsCocomm 𝓞 (Lev Φ n) := isCocomm hnil'
  refine ⟨Lev Φ n, inferInstance, hH, hC, hF, hFin, πL Φ n, πL_surjective Φ n, ker_πL Φ n,
    ?_, ?_, ?_, ?_⟩
  · intro i
    have h := xL_mem_radical hnil' i
    rw [pI_eq] at h
    exact h
  · intro G
    have h := πL_eq_adicEval hnil' G
    rw [pI_eq] at h
    exact h
  · intro i
    have h := comulL_xL hnil' i
    rw [pI_eq] at h
    exact h
  · intro G
    exact counitL_πL (Φ := Φ) (n := n) G

end S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete
end P2MW
export P2MW.S_MvFormalGroup_exists_hopfAlgebra_ker_eq_span_nthSeries_comul_eq_adicEval_of_isAdicComplete (solution)
