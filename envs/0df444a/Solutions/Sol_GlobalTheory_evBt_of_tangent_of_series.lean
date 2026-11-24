-- Prove2me | solution 1 for GlobalTheory.evBt_of_tangent_of_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:48:28.334823+00:00
-- url     : https://prove2.me/submissions/9026ac79-2489-4637-b30c-bc280c6b4938

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvBtStatement
import Definitions.Def_ReciprocityTheory_DualLattices_WFrobStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBtOfTangentOfSeries
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
namespace BtAssembly
variable {R₀ : Type} [CommRing R₀]
private lemma chi_congr {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) {x y : B.G R} (hx : B.map ρ x = 0) (hy : B.map ρ y = 0)
    (h : x = y) : ch.χ ρ hρ ⟨x, hx⟩ = ch.χ ρ hρ ⟨y, hy⟩ := by
  subst h; rfl
private lemma chi_zero {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (h0 : B.map ρ 0 = 0) (k : Fin g) :
    ((ch.χ ρ hρ ⟨0, h0⟩ k : maximalIdeal (R : Type)) : (R : Type)) = 0 := by
  have hsq : (LHom.id R).SqZero := by
    refine ⟨fun a => ⟨a, rfl⟩, ?_⟩
    have : RingHom.ker (LHom.id R).1 = ⊥ := by
      ext a; simp [RingHom.mem_ker, LHom.id]
    rw [this]; simp
  have h := ch.χ_tg ρ hρ (LHom.id R) hsq ρ rfl 0 0 k
  rw [chi_congr ch ρ hρ _ h0 (by simp)] at h
  simpa using h
private lemma chi_nsmul {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (x : B.G R) (hx : B.map ρ x = 0) (n : ℕ)
    (hn : B.map ρ (n • x) = 0) :
    (fun k => ((ch.χ ρ hρ ⟨n • x, hn⟩ k : maximalIdeal (R : Type)) : (R : Type))) =
      nsmulF ch.F (fun k => ((ch.χ ρ hρ ⟨x, hx⟩ k : maximalIdeal (R : Type)) : (R : Type))) n := by
  induction n with
  | zero =>
    funext k
    rw [chi_congr ch ρ hρ hn (map_zero _) (zero_nsmul x), chi_zero]
    rfl
  | succ n ih =>
    have hn' : B.map ρ (n • x) = 0 := by rw [map_nsmul, hx, nsmul_zero]
    have h := ch.χ_add ρ hρ ⟨n • x, hn'⟩ ⟨x, hx⟩
    rw [ih hn'] at h
    rw [chi_congr ch ρ hρ hn (map_add_ker B ρ ⟨n • x, hn'⟩ ⟨x, hx⟩) (succ_nsmul x n)]
    exact h
private lemma nil_of_mem {R K : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ)
    (hK : maximalIdeal (K : Type) = ⊥) (a : maximalIdeal (R : Type)) :
    IsNilpotent (a : (R : Type)) := by
  apply hρ.2
  rw [RingHom.mem_ker]
  have : ρ.1 a ∈ maximalIdeal (K : Type) := fun hu => a.2 (ρ.2.map_nonunit _ hu)
  rw [hK] at this
  exact this
private lemma exists_pow_zero {S : Type} [CommRing S] {g : ℕ} (Y : Fin g → S)
    (h : ∀ l, IsNilpotent (Y l)) : ∃ N : ℕ, ∀ l, Y l ^ N = 0 := by
  choose n hn using h
  refine ⟨∑ l, n l, fun l => pow_eq_zero_of_le ?_ (hn l)⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
private lemma comp_app {R S T : LAlg R₀} (f : LHom R S) (f' : LHom S T) (e : LHom R T)
    (h : f'.comp f = e) (a : (R : Type)) : f'.1 (f.1 a) = e.1 a := by
  subst h; rfl
end BtAssembly
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
open BtAssembly
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ t : TT p g, ∃ t' : B.G D.wd.W,
    B.map D.wd.πW t' = B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) ∧
    ∃ h : B.map D.wd.ρW (p • t') = 0, ∀ k : Fin g, ∃ w : (D.wd.W : Type),
      D.wd.πW.1 w = (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) ∧
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨p • t', h⟩ k : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) = p * (D.wd.b : (D.wd.W : Type)) * w) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → MvPolynomial.coeff m (Γ k) ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀} (wd : WData Tw K) (g : ℕ), WFrobStatement wd g) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvBtStatement D) := by
  intro hTAN hGAM hLAM hWF R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  obtain ⟨hK, hρ1, hL⟩ := hLAM D (Fin.pos k)
  have key : ∀ i : D.fin.ι, ∃ F : (D.fin.AAx i : Type), ∀ φ : LHom (D.fin.AAx i) Tw.O,
      φ.comp (D.fin.sO i) = LHom.id Tw.O → ∀ t : TT p g,
      B.map φ (D.fin.y i) = ptOf B D.L.τ (red p g t) →
      (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) = (Tw.q 0).1 (φ.1 F) := by
    intro i
    obtain ⟨Λ, μ, j, ρΛ, hΛ, hμ, hj, -, hψ⟩ := hL i
    obtain ⟨x, hx⟩ := D.sm.onto (B.map ρΛ (B.map μ (D.fin.y i)))
    have hc : B.map D.wd.ρW (p • x) = 0 := by
      rw [map_nsmul, hx, ← map_nsmul, ← map_nsmul, D.fin.y_p, map_zero, map_zero]
    have hz : B.map ρΛ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) = 0 := by
      rw [map_sub, ← B.map_comp j ρΛ, hj, ← B.map_comp D.wd.πW, D.wd.ρW_eq, hx, sub_self]
    obtain ⟨N, hN⟩ := exists_pow_zero
      (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)))
      (fun l => nil_of_mem ρΛ hΛ hK _)
    obtain ⟨Γ, hΓ, hΓe⟩ := hGAM p D.ch (D.wd.W : Type)
      (fun l => ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hc⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)))
      (fun l => nil_of_mem D.wd.ρW D.sm.nil hK _) (N * 2)
    obtain ⟨Q, hQ⟩ := hWF D.wd g (Γ k) (hΓ k)
    obtain ⟨F, hF⟩ := hμ (j.1 (D.wd.πW.1 ((D.wd.b⁻¹ : (D.wd.W : Type)ˣ) : (D.wd.W : Type))) *
      MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q)
    refine ⟨F, fun φ hφ t ht => ?_⟩
    obtain ⟨ψ, hψμ, hψj, hψρ⟩ := hψ φ hφ
    obtain ⟨t', ht', h, hw⟩ := hTAN D t
    obtain ⟨w, hw1, hw2⟩ := hw k
    have e1 : B.map D.wd.πW t' = B.map ψ (B.map μ (D.fin.y i)) := by
      rw [ht', ← ht, ← B.map_comp, ← B.map_comp, hψμ]
    have hu : B.map D.wd.ρW (t' - x) = 0 := by
      rw [map_sub, hx, ← D.wd.ρW_eq, B.map_comp, e1, ← B.map_comp ψ, hψρ, sub_self]
    have e2 : B.map D.wd.πW (t' - x) =
        B.map ψ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) := by
      rw [map_sub, map_sub, e1, ← B.map_comp j ψ, hψj, B.map_id]
    have e3 : ∀ l, D.wd.πW.1
        ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) =
        ψ.1 ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)) := by
      intro l
      rw [← D.ch.χ_nat D.wd.ρW D.wd.ρ1 D.sm.nil hρ1 D.wd.πW D.wd.ρW_eq ⟨_, hu⟩ l,
        ← D.ch.χ_nat ρΛ D.wd.ρ1 hΛ hρ1 ψ hψρ ⟨_, hz⟩ l]
      rw [chi_congr D.ch D.wd.ρ1 hρ1 _ _ e2]
    have e4 : ∀ l, ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
        (D.wd.W : Type)) ^ (N * 2) = 0 := by
      intro l
      have : ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
          (D.wd.W : Type)) ^ N ∈ RingHom.ker D.wd.πW.1 := by
        rw [RingHom.mem_ker, map_pow, e3, ← map_pow, hN, map_zero]
      rw [D.wd.ker_πW, Ideal.mem_span_singleton'] at this
      obtain ⟨a, ha⟩ := this
      rw [pow_mul, ← ha, mul_pow, D.wd.p_sq, mul_zero]
    have hpu : B.map D.wd.ρW (p • (t' - x)) = 0 := by rw [map_nsmul, hu, nsmul_zero]
    have e5 := D.ch.χ_add D.wd.ρW D.sm.nil ⟨_, hc⟩ ⟨_, hpu⟩
    rw [chi_nsmul D.ch D.wd.ρW D.sm.nil _ hu p hpu, hΓe _ e4,
      chi_congr D.ch D.wd.ρW D.sm.nil _ h
        (show p • x + p • (t' - x) = p • t' by rw [← nsmul_add, add_sub_cancel])] at e5
    have e6 := congrFun e5 k
    rw [hw2] at e6
    obtain ⟨a, ha⟩ := D.wd.πW_surj (MvPolynomial.eval (fun l => D.wd.πW.1
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type))) Q)
    have e7 := hQ _ (by
      rw [← e6, mul_assoc]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) a ha
    rw [← e6] at e7
    have e8 : D.wd.πW.1 ((D.wd.b : (D.wd.W : Type)) * w - a) = 0 := by
      rw [← D.wd.ann_p, mul_sub, ← mul_assoc, e7, sub_self]
    rw [map_sub, sub_eq_zero] at e8
    have e9 : ψ.1 (MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q) =
        D.wd.πW.1 a := by
      rw [ha]
      have hid : (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type)).comp
          (j.1 : (Tw.R 0 : Type) →+* (Λ : Type)) = RingHom.id _ :=
        RingHom.ext fun b => comp_app j ψ _ hψj b
      have := MvPolynomial.eval₂_comp_left (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type))
        (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q
      rw [hid] at this
      refine this.trans ?_
      rw [MvPolynomial.eval₂_id]
      congr 2
      funext l
      exact (e3 l).symm
    have e10 : (Tw.q 0).1 (φ.1 F) = ψ.1 (μ.1 F) := (comp_app μ ψ _ hψμ F).symm
    rw [e10, hF, map_mul, e9, comp_app j ψ _ hψj, ← hw1, ← e8]
    change _ = D.wd.πW.1 _ * _
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  choose F hF using key
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  have hs := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  have h := hF (D.ptIdx (red p g t)) (D.ptMap (red p g t)) hs.1 t hs.2.1
  have hm : (D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hm
  obtain ⟨r, hr⟩ := hm
  refine ⟨r, ?_⟩
  rw [mul_comm, hr, map_sub]
  rfl
end GlobalTheory
