-- Prove2me | solution 1 for GlobalTheory.chart_p_smul_lift_eq_bt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:13.428772+00:00
-- url     : https://prove2.me/submissions/7c8100b0-c5cb-4160-98a8-cc4760d4aab6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvBtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChartPSmulLiftEqBt
import Theorems.Thm_ReciprocityTheory_PGsh_LHom_sqZero_of_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
section
variable {R₀ : Type} [CommRing R₀] {g : ℕ} {V : Type} [AddCommGroup V] [Module R₀ V]
private lemma btTanCrd_tmul (gb : Module.Basis (Fin g) R₀ V) {M : Type} [AddCommGroup M]
    [Module R₀ M] (k : Fin g) (w : V) (m : M) :
    btTanCrd gb M k (w ⊗ₜ m) = gb.repr w k • m := by
  simp [btTanCrd]
private lemma btTanCrd_nat (gb : Module.Basis (Fin g) R₀ V) {M N : Type} [AddCommGroup M]
    [Module R₀ M] [AddCommGroup N] [Module R₀ N] (f : M →ₗ[R₀] N) (k : Fin g) (v : V ⊗[R₀] M) :
    btTanCrd gb N k (LinearMap.lTensor V f v) = f (btTanCrd gb M k v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul w m => simp [btTanCrd_tmul]
  | add x y hx hy => simp [hx, hy]
private lemma btTanCrd_base (gb : Module.Basis (Fin g) R₀ V) {S : Type} [CommRing S]
    [Algebra R₀ S] (k : Fin g) (v : V ⊗[R₀] S) :
    (Module.Basis.baseChange S gb).repr (TensorProduct.comm R₀ V S v) k = btTanCrd gb S k v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul w m => simp [btTanCrd_tmul]
  | add x y hx hy => simp [hx, hy]
end
private lemma btTan_chi_tg {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀}
    (ch : FormalChartAtZero B K g) {R S : LAlg R₀}
    (hF : ∀ a : Fin g → (R : Type), (∀ i, IsNilpotent (a i)) →
      ∃ M : Matrix (Fin g) (Fin g) (R : Type),
        (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) (R : Type)) k j ∈ Ideal.span (Set.range a)) ∧
        ∀ e : Fin g → (R : Type), (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e)
    (ρ : LHom R K) (hρ : IsNilOver ρ) (π : LHom R S) (hπ : π.SqZero)
    (ρS : LHom S K) (hfac : ρS.comp π = ρ) (v : B.gg ⊗[R₀] π.ker) (k : Fin g) :
    ((ch.χ ρ hρ ⟨B.tg π hπ v, map_tg_ker B ρ π hπ ρS hfac _⟩ k : maximalIdeal (R : Type)) :
      (R : Type)) = (btTanCrd ch.gb π.ker k v : (R : Type)) := by
  have hmul : ∀ x ∈ RingHom.ker π.1, ∀ y ∈ RingHom.ker π.1, x * y = 0 := by
    intro x hx y hy
    have := Ideal.mul_mem_mul hx hy
    rw [← pow_two, hπ.2] at this
    exact this
  induction v using TensorProduct.induction_on generalizing k with
  | zero =>
    have := ch.χ_tg ρ hρ π hπ ρS hfac 0 0 k
    simpa using this
  | tmul w m =>
    rw [ch.χ_tg ρ hρ π hπ ρS hfac w m k, btTanCrd_tmul]; rfl
  | add x y hx hy =>
    have h := congrFun (ch.χ_add ρ hρ ⟨B.tg π hπ x, map_tg_ker B ρ π hπ ρS hfac _⟩
      ⟨B.tg π hπ y, map_tg_ker B ρ π hπ ρS hfac _⟩) k
    simp only [hx, hy] at h
    obtain ⟨M, hM, hMe⟩ := hF (fun k => (btTanCrd ch.gb π.ker k x : (R : Type)))
      (fun i => ⟨2, by rw [pow_two]; exact hmul _ (btTanCrd ch.gb π.ker i x).2 _ (btTanCrd ch.gb π.ker i x).2⟩)
    rw [hMe _ (fun i j => hmul _ (btTanCrd ch.gb π.ker i y).2 _ (btTanCrd ch.gb π.ker j y).2)] at h
    have hle : Ideal.span (Set.range fun k => (btTanCrd ch.gb π.ker k x : (R : Type))) ≤
        RingHom.ker π.1 := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (btTanCrd ch.gb π.ker i x).2
    have h0 : ((M - 1) *ᵥ fun k => (btTanCrd ch.gb π.ker k y : (R : Type))) k = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      exact hmul _ (hle (hM k j)) _ (btTanCrd ch.gb π.ker j y).2
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at h0
    rw [Pi.add_apply, h0] at h
    simp only [map_add, Submodule.coe_add]
    exact h
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ t : TT p g, ∃ t' : B.G D.wd.W,
    B.map D.wd.πW t' = B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) ∧
    ∃ h : B.map D.wd.ρW (p • t') = 0, ∀ k : Fin g, ∃ w : (D.wd.W : Type),
      D.wd.πW.1 w = (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) ∧
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨p • t', h⟩ k : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) = p * (D.wd.b : (D.wd.W : Type)) * w) := by
  intro hF R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D t
  choose th w hth hpth hw using fun i => D.L.bt_spec i 1
  have hsq : D.wd.πW.SqZero := D.wd.πW.sqZero_of_span (p : (D.wd.W : Type)) D.wd.πW_surj
    D.wd.ker_πW (by rw [← pow_two]; exact D.wd.p_sq)
  have hc1 : D.wd.πW.comp D.wd.ψ = (Tw.r 0).comp (Tw.π 1) :=
    Subtype.ext (AlgHom.ext fun a => D.wd.compat a)
  have hc2 : (Tw.r 0).comp (Tw.q 1) = Tw.q 0 :=
    Subtype.ext (AlgHom.ext fun a => Tw.r_q 0 a)
  have hf : ∀ a ∈ (Tw.π 1).ker, D.wd.ψ.1.toLinearMap a ∈ D.wd.πW.ker := by
    intro a ha
    change D.wd.πW.1 (D.wd.ψ.1 a) = 0
    change (Tw.π 1).1 a = 0 at ha
    rw [D.wd.compat, ha, map_zero]
  let n : Ix g → ℕ := fun i => (red p g t i).val
  let v : B.gg ⊗[R₀] D.wd.πW.ker := ∑ i, n i • LinearMap.lTensor B.gg
    (D.wd.ψ.1.toLinearMap.restrict hf)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π 1) (Tw.ξ 1) (Tw.ξ_mem 1)) (w i))
  have hpt : p • ∑ i, n i • B.map D.wd.ψ (p • th i) = B.tg D.wd.πW hsq v := by
    simp only [v, map_sum, map_nsmul (B.tg D.wd.πW hsq), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [B.tg_nat (Tw.π 1) D.wd.πW (Tw.sqZero 1) hsq, ← hpth, smul_comm p, ← map_nsmul,
      smul_smul, pow_two]
  refine ⟨∑ i, n i • B.map D.wd.ψ (p • th i), ?_, ?_⟩
  · simp only [ptOf, map_sum, map_nsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← B.map_comp, hc1, B.map_comp, hth, ← B.map_comp, hc2, D.L.τ_compat i 0, map_nsmul]
  · refine ⟨hpt ▸ map_tg_ker B _ _ hsq _ D.wd.ρW_eq v, fun k => ?_⟩
    refine ⟨∑ i, n i • D.wd.ψ.1 (btTanCrd D.ch.gb _ k (w i)), ?_, ?_⟩
    · simp only [map_sum, map_nsmul, Matrix.mulVec, dotProduct, map_mul, Function.comp_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := congrArg (btTanCrd D.ch.gb _ k) (hw i)
      rw [btTanCrd_nat, btTanCrd_nat] at h1
      simp only [AlgHom.toLinearMap_apply] at h1
      rw [D.wd.compat, h1, Tw.r_q, D.L.Bt_eq, btTanCrd_base]
      have h2 : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) (t i)) = (n i : (Tw.R 0 : Type)) := by
        have h3 : t i - (n i : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
          rw [RingHom.mem_ker, map_sub, map_natCast]
          simp only [n, red]
          rw [ZMod.natCast_zmod_val, sub_self]
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h3
        obtain ⟨c, hc⟩ := h3
        have hp0 : (Tw.q 0).1 (p : (Tw.O : Type)) = 0 := by
          rw [← RingHom.mem_ker, D.tower_zero_ker]; exact Ideal.subset_span rfl
        rw [eq_add_of_sub_eq hc.symm]
        simp only [map_add, map_mul, map_natCast (algebraMap ℤ_[p] (Tw.O : Type)), hp0]
        simp
      rw [h2, nsmul_eq_mul, mul_comm]
    · have h := btTan_chi_tg D.ch (hF D.ch _) D.wd.ρW D.sm.nil D.wd.πW hsq D.wd.ρ1 D.wd.ρW_eq v k
      simp only [hpt]
      rw [h]
      simp only [v, map_sum, map_nsmul, AddSubmonoidClass.coe_finset_sum,
        AddSubmonoidClass.coe_nsmul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [btTanCrd_nat, ← LinearMap.lTensor_def, btTanCrd_nat, ← D.wd.ξ_img, mul_smul_comm,
        ← map_mul]
      congr 1
end GlobalTheory
