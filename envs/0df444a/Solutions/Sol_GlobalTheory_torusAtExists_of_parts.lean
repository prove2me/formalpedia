-- Prove2me | solution 1 for GlobalTheory.torusAtExists_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:26.115811+00:00
-- url     : https://prove2.me/submissions/a018d280-2a9e-4e88-b27b-568e6e340926

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open NumberField
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∀ x ∈ X.dom, ∃ e : X.Ψ → Fin r → (Fin r → ℂ), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) ∧ ∀ τ (i : ℕ) (hi : i ≤ r), Submodule.span ℂ (Set.range fun a : Fin i => e τ (Fin.castLE hi a)) = Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE hi a))) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ b : Module.Basis (Fin (2 * (X.Ψ.card * r))) ℝ (X.Ψ → Fin r → ℂ), ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ ∃ v ∈ X.Λ, (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) = y) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ u v : Fin r → E, ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)).im = sg * ((Algebra.trace ℚ E (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) → ∃ (dim : (E →+* ℂ) → ℕ) (hp : ∀ τ : X.Ψ, dim τ.1 = X.p0) (hn : ∀ τ : X.Ψ, dim (ComplexEmbedding.conjugate τ.1) = r - X.p0) (Φ : (X.Ψ → Fin r → ℂ) ≃ₗ[ℝ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim), Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim) = X.Ψ.card * r ∧ (∀ τ, dim τ + dim (ComplexEmbedding.conjugate τ) = r) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim τ.1)), (Φ y) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ (Fin.castLE (by rw [hp τ]; exact X.p0_le) a))) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim (ComplexEmbedding.conjugate τ.1))), (Φ y) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * (starRingEnd ℂ) (-_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (hn τ); have := X.p0_le; omega⟩))) ∧ (∀ (α : 𝓞 E) y, Φ (fun τ => τ.1 (α : E) • y τ) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (Φ y)) ∧ ∀ y y', (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (Φ y) (Φ y')).im = ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (y' τ)).im) → (∀ (E : Type) [Field E] [NumberField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E), ∃ s ∈ X.Sec 1 1, s ≠ 0) → _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtExistsStatement := by
  intro hframe hbasis hsign hiso hsec
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtExistsStatement
  intro E _ _ _ r X hperf w0 hpar x hx
  obtain ⟨e, he_orth, he_flag⟩ := hframe E r X x hx
  obtain ⟨bas, hbas⟩ := hbasis E r X
  obtain ⟨sg, hsg, hsgeq⟩ := hsign E r X
  obtain ⟨dim, hp, hn, Φ, hcard, hdim, hpos, hneg, hact, him⟩ := hiso E r X e he_orth
  have hint : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    exact map_isIntegral_int (IsCMField.complexConj E) w0.isIntegral_coe
  let w' : 𝓞 E := ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E), hint⟩
  have hw' : (w' : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) := rfl
  let φ : (Fin r → E) →+ _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim :=
    { toFun := fun v => Φ (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)
      map_zero' := by
        have h : (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (0 : Fin r → E)) = 0 := by
          funext τ a
          simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        simp only [h, map_zero]
      map_add' := fun u v => by
        have h : (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (u + v)) =
            (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 u) + (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) := by
          funext τ a
          simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        simp only [h, map_add] }
  have hφ : ∀ v, φ v = Φ (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) := fun v => rfl
  have hsmul : ∀ (α : 𝓞 E) (v : Fin r → E), α • v = (α : E) • v := fun α v => by
    funext i
    rfl
  have hφactE : ∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (φ v) := by
    intro α v
    rw [hφ, hφ, ← hact]
    congr 1
    funext τ a
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, map_mul]
  have hφact : ∀ (α : 𝓞 E) (v : Fin r → E), φ (α • v) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (φ v) := by
    intro α v
    rw [hsmul, hφactE]
  have himφ : ∀ u v, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (φ u) (φ v)).im =
      sg * ((Algebra.trace ℚ E (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ) := fun u v =>
    (him _ _).trans (hsgeq u v)
  let bT : Module.Basis (Fin (2 * Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim))) ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) :=
    (bas.map Φ).reindex (finCongr (by rw [hcard]))
  have hL : ∀ y, y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT ↔ ∃ v ∈ X.Λ, φ v = y := by
    intro y
    have hrange : Set.range bT = (Φ.toLinearMap.restrictScalars ℤ) '' Set.range bas := by
      ext z
      simp only [bT, Module.Basis.range_reindex, Set.mem_range, Set.mem_image,
        Module.Basis.map_apply, exists_exists_eq_and, LinearMap.coe_restrictScalars,
        LinearEquiv.coe_coe]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.lat
    rw [hrange, Submodule.span_image, Submodule.mem_map]
    constructor
    · rintro ⟨y0, hy0, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (hbas y0).1 hy0
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, (hbas _).2 ⟨v, hv, rfl⟩, rfl⟩
  have hmem : ∀ v ∈ X.Λ, φ v ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT := fun v hv => (hL _).2 ⟨v, hv, rfl⟩
  have stable : ∀ (α : 𝓞 E) (y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim), y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT → _root_.ReciprocityTheory.ChartRestriction.G.I2.act α y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT := by
    intro α y hy
    obtain ⟨v, hv, rfl⟩ := (hL y).1 hy
    rw [← hφact]
    exact hmem _ (X.Λ.smul_mem α hv)
  have par : ∀ y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT, ∀ z ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT, ∃ k : ℤ,
      (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w0 z)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w' z)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y z).im = 2 * k := by
    intro y hy z hz
    obtain ⟨u, hu, rfl⟩ := (hL y).1 hy
    obtain ⟨v, hv, rfl⟩ := (hL z).1 hz
    obtain ⟨k, hk⟩ := hpar u hu v hv
    have hsub : (w0 - w') • v = ((w0 : E) - _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) • v := by
      rw [hsmul]
      rfl
    have hsplit : φ (w0 • v) = φ ((w0 - w') • v) + φ (w' • v) := by
      rw [← map_add, ← add_smul, sub_add_cancel]
    rw [← hφact, ← hφact, hsplit, _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right, himφ, himφ, himφ, hsub]
    have hkR := congrArg (fun q : ℚ => (q : ℝ)) hk
    push_cast at hkR
    rcases hsg with rfl | rfl
    · exact ⟨k, by linarith⟩
    · exact ⟨-k, by push_cast; linarith⟩
  have hneg0 : ∀ y z : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (-y) z).im = -(_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y z).im := by
    intro y z
    have h := _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_left y (-y) z
    rw [add_neg_cancel] at h
    have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) z).im = 0 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf]
    linarith
  have perfect : ∀ ψ : _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT →+ ℤ, ∃ y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT, ∀ z : _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT,
      (ψ z : ℝ) = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y (z : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim)).im := by
    intro ψ
    let g : X.Λ →+ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT :=
      (φ.comp X.Λ.subtype.toAddMonoidHom).codRestrict (_root_.ReciprocityTheory.ChartRestriction.G.I2.lat bT) (fun v => hmem v v.2)
    obtain ⟨u, hu, hχ⟩ := hperf (ψ.comp g)
    have hval : ∀ v (hv : v ∈ X.Λ), (ψ ⟨φ v, hmem v hv⟩ : ℝ) =
        ((Algebra.trace ℚ E (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ) := by
      intro v hv
      have h := congrArg (fun q : ℚ => (q : ℝ)) (hχ ⟨v, hv⟩)
      push_cast at h
      exact h
    rcases hsg with rfl | rfl
    · refine ⟨φ u, hmem u hu, fun z => ?_⟩
      obtain ⟨v, hv, hvz⟩ := (hL z).1 z.2
      obtain rfl : z = ⟨φ v, hmem v hv⟩ := Subtype.ext hvz.symm
      rw [hval v hv]
      show _ = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (φ u) (φ v)).im
      rw [himφ]
      ring
    · refine ⟨-φ u, neg_mem (hmem u hu), fun z => ?_⟩
      obtain ⟨v, hv, hvz⟩ := (hL z).1 z.2
      obtain rfl : z = ⟨φ v, hmem v hv⟩ := Subtype.ext hvz.symm
      rw [hval v hv]
      show _ = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (-φ u) (φ v)).im
      rw [hneg0, himφ]
      ring
  let T : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E := _root_.GlobalTheory.TorusAtAssembly.torus (dim := dim) (b := bT) (w := w0) (w' := w')
    r hdim hw' stable par perfect
  obtain ⟨s, hs, hs0⟩ := hsec E T
  refine ⟨
    { T := T
      φ := φ
      sg := sg
      sg_pm := hsg
      dim_pos := hp
      dim_neg := hn
      e := e
      e_orth := he_orth
      e_flag := he_flag
      coord_pos := fun τ a v => hpos _ τ a
      coord_neg := fun τ a v => hneg _ τ a
      w0 := w0
      act_eq := hφactE
      lat := hL
      im_eq := fun u _ v _ => himφ u v
      eps_eq := ?_
      s := s
      s_mem := hs
      s_ne := hs0 }, rfl⟩
  intro v hv
  have hv' : (w0 : E) • v ∈ X.Λ := by
    rw [← hsmul]
    exact X.Λ.smul_mem w0 hv
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.TorusAtAssembly.integral_of_parity hw' par (φ v) (φ ((w0 : E) • v))
    (hmem v hv) (hmem _ hv')
  show ((_root_.GlobalTheory.TorusAtAssembly.sgnFloor (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (φ v) (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w0 (φ v))).im : ℤ) : ℝ) = _
  rw [← hφactE, hk, _root_.GlobalTheory.TorusAtAssembly.sgnFloor_cos]
  congr 2
  exact hk.symm
end _root_.GlobalTheory
end GlobalTheory
