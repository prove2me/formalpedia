-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isGaugeMajorised3_of_mem_gl3CyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b82355ad-06db-52f2-83a9-d22e8b289d90

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isGaugeMajorised3_of_mem_gl3CyclicSubspace

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

namespace SpanMajorisation

namespace MirabolicMajorantSupport

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem norm_eq_one_of_valued_eq_one {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    ‖x‖ = 1 :=
  le_antisymm (Valued.toNormedField.norm_le_one_iff.2 hx.le)
    (Valued.toNormedField.one_le_norm_iff.2 hx.ge)

private theorem norm_le_one_of_valued_le_one {x : v.adicCompletion F} (hx : Valued.v x ≤ 1) :
    ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.2 hx

private theorem valued_mul2_lt_one {b c : v.adicCompletion F} (hb : Valued.v b ≤ 1)
    (hc : Valued.v c < 1) : Valued.v (b * c) < 1 := by
  rw [Valuation.map_mul]
  calc Valued.v b * Valued.v c ≤ 1 * Valued.v c := mul_le_mul' hb le_rfl
    _ = Valued.v c := one_mul _
    _ < 1 := hc

private theorem valued_mul3_lt_one {a b c : v.adicCompletion F} (ha : Valued.v a ≤ 1)
    (hb : Valued.v b ≤ 1) (hc : Valued.v c < 1) : Valued.v (a * b * c) < 1 :=
  valued_mul2_lt_one (by rw [Valuation.map_mul]; exact mul_le_one' ha hb) hc

private theorem valued_sub_lt_one {x y : v.adicCompletion F} (hx : Valued.v x < 1)
    (hy : Valued.v y < 1) : Valued.v (x - y) < 1 :=
  lt_of_le_of_lt (Valuation.map_sub _ x y) (max_lt hx hy)

private theorem valued_add_lt_one {x y : v.adicCompletion F} (hx : Valued.v x < 1)
    (hy : Valued.v y < 1) : Valued.v (x + y) < 1 :=
  lt_of_le_of_lt (Valuation.map_add _ x y) (max_lt hx hy)

variable (k : GL (Fin 3) (v.adicCompletion F))
  (hk : ∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1)
  (hd : Valued.v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det = 1)

include hk hd in
private theorem exists_lastRow_valued_eq_one :
    ∃ j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) 2 j) = 1 := by
  by_contra h
  have hlt : ∀ j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) 2 j) < 1 :=
    fun j => lt_of_le_of_ne (hk 2 j) fun e => h ⟨j, e⟩
  have hdet : Valued.v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det < 1 := by
    rw [Matrix.det_fin_three]
    refine valued_sub_lt_one (valued_add_lt_one (valued_add_lt_one (valued_sub_lt_one
      (valued_sub_lt_one ?_ ?_) ?_) ?_) ?_) ?_
    · exact valued_mul3_lt_one (hk 0 0) (hk 1 1) (hlt 2)
    · exact valued_mul3_lt_one (hk 0 0) (hk 1 2) (hlt 1)
    · exact valued_mul3_lt_one (hk 0 1) (hk 1 0) (hlt 2)
    · exact valued_mul3_lt_one (hk 0 1) (hk 1 2) (hlt 0)
    · exact valued_mul3_lt_one (hk 0 2) (hk 1 0) (hlt 1)
    · exact valued_mul3_lt_one (hk 0 2) (hk 1 1) (hlt 0)
  exact absurd hd hdet.ne

include hk in
private theorem valued_bottomMinor_le_one (j j' : Fin 3) : Valued.v (bottomMinor k j j') ≤ 1 := by
  unfold bottomMinor
  refine Valuation.map_sub_le _ ?_ ?_ <;>
    · rw [Valuation.map_mul]; exact mul_le_one' (hk _ _) (hk _ _)

private theorem det_eq_minors :
    (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) 0 0 * bottomMinor k 1 2 -
        (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) 0 1 * bottomMinor k 0 2 +
        (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) 0 2 * bottomMinor k 0 1 := by
  rw [Matrix.det_fin_three]
  unfold bottomMinor
  ring

include hk hd in
private theorem exists_bottomMinor_valued_eq_one :
    Valued.v (bottomMinor k 0 1) = 1 ∨ Valued.v (bottomMinor k 0 2) = 1 ∨
      Valued.v (bottomMinor k 1 2) = 1 := by
  by_contra h
  have l01 := lt_of_le_of_ne (valued_bottomMinor_le_one k hk 0 1) fun e => h (Or.inl e)
  have l02 := lt_of_le_of_ne (valued_bottomMinor_le_one k hk 0 2) fun e => h (Or.inr (Or.inl e))
  have l12 := lt_of_le_of_ne (valued_bottomMinor_le_one k hk 1 2) fun e => h (Or.inr (Or.inr e))
  have hdet : Valued.v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det < 1 := by
    rw [det_eq_minors]
    refine valued_add_lt_one (valued_sub_lt_one ?_ ?_) ?_
    · exact valued_mul2_lt_one (hk 0 0) l12
    · exact valued_mul2_lt_one (hk 0 1) l02
    · exact valued_mul2_lt_one (hk 0 2) l01
  exact absurd hd hdet.ne

include hk hd in
private theorem lastRowSup_eq_one_of_integral : lastRowSup k = 1 := by
  obtain ⟨j, hj⟩ := exists_lastRow_valued_eq_one k hk hd
  have hle : ∀ j', ‖(k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) 2 j'‖ ≤ 1 :=
    fun j' => norm_le_one_of_valued_le_one (hk 2 j')
  have hj' := norm_eq_one_of_valued_eq_one hj
  unfold lastRowSup
  apply le_antisymm (max_le (max_le (hle 0) (hle 1)) (hle 2))
  fin_cases j
  · exact hj'.symm.le.trans (le_max_left _ _ |>.trans (le_max_left _ _))
  · exact hj'.symm.le.trans (le_max_right _ _ |>.trans (le_max_left _ _))
  · exact hj'.symm.le.trans (le_max_right _ _)

include hk hd in
private theorem minorSup_eq_one_of_integral : minorSup k = 1 := by
  have hle : ∀ j j', ‖bottomMinor k j j'‖ ≤ 1 :=
    fun j j' => norm_le_one_of_valued_le_one (valued_bottomMinor_le_one k hk j j')
  unfold minorSup
  apply le_antisymm (max_le (max_le (hle 0 1) (hle 0 2)) (hle 1 2))
  rcases exists_bottomMinor_valued_eq_one k hk hd with h | h | h
  · exact (norm_eq_one_of_valued_eq_one h).symm.le.trans
      (le_max_left _ _ |>.trans (le_max_left _ _))
  · exact (norm_eq_one_of_valued_eq_one h).symm.le.trans
      (le_max_right _ _ |>.trans (le_max_left _ _))
  · exact (norm_eq_one_of_valued_eq_one h).symm.le.trans (le_max_right _ _)

include hd in
private theorem detSize_eq_one_of_integral : detSize k = 1 :=
  norm_eq_one_of_valued_eq_one hd

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem finRoot₁_eq_one_of_integral (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F)
    (hk : ∀ i j, Valued.v ((componentAt3 (𝓞 F) F v g :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1)
    (hd : Valued.v (componentAt3 (𝓞 F) F v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det = 1) :
    finRoot₁ F v g = 1 := by
  unfold finRoot₁
  rw [detSize_eq_one_of_integral _ hd, lastRowSup_eq_one_of_integral _ hk hd,
    minorSup_eq_one_of_integral _ hk hd]
  norm_num

private theorem finRoot₂_eq_one_of_integral (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F)
    (hk : ∀ i j, Valued.v ((componentAt3 (𝓞 F) F v g :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1)
    (hd : Valued.v (componentAt3 (𝓞 F) F v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det = 1) :
    finRoot₂ F v g = 1 := by
  unfold finRoot₂
  rw [lastRowSup_eq_one_of_integral _ hk hd, minorSup_eq_one_of_integral _ hk hd]
  norm_num

private theorem eventually_valued_le_one (x : AdeleRing (𝓞 F) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v ((AdelicLevel.finAdeleEval (𝓞 F) F v) (AdelicLevel.adeleFin (𝓞 F) F x)) ≤ 1 :=
  (x.2).2

private theorem componentAt3_apply (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F)
    (i j : Fin 3) :
    (componentAt3 (𝓞 F) F v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j =
      (AdelicLevel.finAdeleEval (𝓞 F) F v) (AdelicLevel.adeleFin (𝓞 F) F
        ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) i j)) :=
  rfl

private theorem det_componentAt3 (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) :
    (componentAt3 (𝓞 F) F v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det =
      ((AdelicLevel.finAdeleEval (𝓞 F) F v).comp (AdelicLevel.adeleFin (𝓞 F) F))
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)).det := by
  change (((AdelicLevel.finAdeleEval (𝓞 F) F v).comp (AdelicLevel.adeleFin (𝓞 F) F)).mapMatrix
    (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F))).det = _
  exact (RingHom.map_det _ _).symm

private theorem eventually_integral_componentAt3 (g : AdelicGL 3 (𝓞 F) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, Valued.v ((componentAt3 (𝓞 F) F v g :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1) ∧
      Valued.v (componentAt3 (𝓞 F) F v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det = 1 := by
  set G : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F) :=
    (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) with hG
  set u : (AdeleRing (𝓞 F) F)ˣ := Matrix.GeneralLinearGroup.det g with hu
  have hmul : G.det * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 1 := Units.mul_inv u
  have h_entries : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
      Valued.v ((componentAt3 (𝓞 F) F v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    filter_upwards [eventually_valued_le_one F (G i j)] with v hv
    rw [componentAt3_apply]
    exact hv
  have h_det : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (componentAt3 (𝓞 F) F v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)).det = 1 := by
    filter_upwards [eventually_valued_le_one F G.det,
      eventually_valued_le_one F ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] with v h₁ h₂
    rw [det_componentAt3]
    set φ := (AdelicLevel.finAdeleEval (𝓞 F) F v).comp (AdelicLevel.adeleFin (𝓞 F) F) with hφ
    have hprod : Valued.v (φ G.det) * Valued.v (φ ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        = 1 := by
      rw [← Valuation.map_mul, ← map_mul, hmul, map_one, Valuation.map_one]
    have h₁' : Valued.v (φ G.det) ≤ 1 := h₁
    have h₂' : Valued.v (φ ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ≤ 1 := h₂
    have h₃ : Valued.v (φ G.det) * Valued.v (φ ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ≤
        Valued.v (φ G.det) * 1 := mul_le_mul' le_rfl h₂'
    rw [hprod, mul_one] at h₃
    exact le_antisymm h₁' h₃
  exact h_entries.and h_det

private theorem mulSupport_finRootProd_finite (g : AdelicGL 3 (𝓞 F) F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => finRoot₁ F v g * finRoot₂ F v g).Finite := by
  refine (Filter.eventually_cofinite.1 (eventually_integral_componentAt3 F g)).subset fun v hv hint => ?_
  rw [Function.mem_mulSupport] at hv
  exact hv (by rw [finRoot₁_eq_one_of_integral F v g hint.1 hint.2,
    finRoot₂_eq_one_of_integral F v g hint.1 hint.2, one_mul])

private theorem mulSupport_finRoot₁_finite (g : AdelicGL 3 (𝓞 F) F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => finRoot₁ F v g).Finite := by
  refine (Filter.eventually_cofinite.1 (eventually_integral_componentAt3 F g)).subset fun v hv hint => ?_
  rw [Function.mem_mulSupport] at hv
  exact hv (finRoot₁_eq_one_of_integral F v g hint.1 hint.2)

private theorem mulSupport_finRoot₂_finite (g : AdelicGL 3 (𝓞 F) F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => finRoot₂ F v g).Finite := by
  refine (Filter.eventually_cofinite.1 (eventually_integral_componentAt3 F g)).subset fun v hv hint => ?_
  rw [Function.mem_mulSupport] at hv
  exact hv (finRoot₂_eq_one_of_integral F v g hint.1 hint.2)

end Adelic

end MirabolicMajorantSupport

end SpanMajorisation

noncomputable section

namespace SpanMajorisation
namespace MirabolicMajorantTranslate

section Local

variable {L : Type*} [NormedField L]

private def IsIntegralUnit3 (n : GL (Fin 3) L) : Prop :=
  (∀ i j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) ∧
    ∀ i j, ‖((n⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1

private theorem entry_mul (k n : GL (Fin 3) L) (i j : Fin 3) :
    ((k * n : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j =
      (k : Matrix (Fin 3) (Fin 3) L) i 0 * (n : Matrix (Fin 3) (Fin 3) L) 0 j +
        (k : Matrix (Fin 3) (Fin 3) L) i 1 * (n : Matrix (Fin 3) (Fin 3) L) 1 j +
          (k : Matrix (Fin 3) (Fin 3) L) i 2 * (n : Matrix (Fin 3) (Fin 3) L) 2 j := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem bottomMinor_mul (k n : GL (Fin 3) L) (j j' : Fin 3) :
    bottomMinor (k * n) j j' =
      bottomMinor k 0 1 * ((n : Matrix (Fin 3) (Fin 3) L) 0 j * (n : Matrix (Fin 3) (Fin 3) L) 1 j' -
          (n : Matrix (Fin 3) (Fin 3) L) 0 j' * (n : Matrix (Fin 3) (Fin 3) L) 1 j) +
        bottomMinor k 0 2 * ((n : Matrix (Fin 3) (Fin 3) L) 0 j * (n : Matrix (Fin 3) (Fin 3) L) 2 j' -
          (n : Matrix (Fin 3) (Fin 3) L) 0 j' * (n : Matrix (Fin 3) (Fin 3) L) 2 j) +
          bottomMinor k 1 2 * ((n : Matrix (Fin 3) (Fin 3) L) 1 j * (n : Matrix (Fin 3) (Fin 3) L) 2 j' -
            (n : Matrix (Fin 3) (Fin 3) L) 1 j' * (n : Matrix (Fin 3) (Fin 3) L) 2 j) := by
  simp only [bottomMinor, entry_mul]
  ring

private theorem detSize_mul_eq_mul (k n : GL (Fin 3) L) : detSize (k * n) = detSize k * detSize n := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, norm_mul]

private theorem entry_le_lastRowSup (k : GL (Fin 3) L) (j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ lastRowSup k := by
  unfold lastRowSup
  fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem minor_le_minorSup_01 (k : GL (Fin 3) L) : ‖bottomMinor k 0 1‖ ≤ minorSup k :=
  (le_max_left _ _).trans (le_max_left _ _)

private theorem minor_le_minorSup_02 (k : GL (Fin 3) L) : ‖bottomMinor k 0 2‖ ≤ minorSup k :=
  (le_max_right _ _).trans (le_max_left _ _)

private theorem minor_le_minorSup_12 (k : GL (Fin 3) L) : ‖bottomMinor k 1 2‖ ≤ minorSup k :=
  le_max_right _ _

variable [IsUltrametricDist L]

private theorem norm_sub_le_max' (x y : L) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  simpa only [norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

private theorem norm_add3_le {x y z : L} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖x + y + z‖ ≤ R :=
  (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)) hz)

private theorem norm_mul_le_of_le {x y : L} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ R := by
  rw [norm_mul]
  calc ‖x‖ * ‖y‖ ≤ ‖x‖ * 1 := by gcongr
    _ = ‖x‖ := mul_one _
    _ ≤ R := hx

private theorem minor_of_integral_le_one {n : GL (Fin 3) L}
    (hn : ∀ i j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) (a b j j' : Fin 3) :
    ‖(n : Matrix (Fin 3) (Fin 3) L) a j * (n : Matrix (Fin 3) (Fin 3) L) b j' -
        (n : Matrix (Fin 3) (Fin 3) L) a j' * (n : Matrix (Fin 3) (Fin 3) L) b j‖ ≤ 1 :=
  (norm_sub_le_max' _ _).trans
    (max_le (norm_mul_le_of_le (hn a j) (hn b j')) (norm_mul_le_of_le (hn a j') (hn b j)))

private theorem lastRowSup_mul_le {n : GL (Fin 3) L}
    (hn : ∀ i j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) (k : GL (Fin 3) L) :
    lastRowSup (k * n) ≤ lastRowSup k := by
  have h : ∀ j, ‖((k * n : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ lastRowSup k := by
    intro j
    rw [entry_mul]
    exact norm_add3_le (norm_mul_le_of_le (entry_le_lastRowSup k 0) (hn 0 j))
      (norm_mul_le_of_le (entry_le_lastRowSup k 1) (hn 1 j))
      (norm_mul_le_of_le (entry_le_lastRowSup k 2) (hn 2 j))
  exact max_le (max_le (h 0) (h 1)) (h 2)

private theorem minorSup_mul_le {n : GL (Fin 3) L}
    (hn : ∀ i j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) (k : GL (Fin 3) L) :
    minorSup (k * n) ≤ minorSup k := by
  have h : ∀ j j', ‖bottomMinor (k * n) j j'‖ ≤ minorSup k := by
    intro j j'
    rw [bottomMinor_mul]
    exact norm_add3_le (norm_mul_le_of_le (minor_le_minorSup_01 k) (minor_of_integral_le_one hn 0 1 j j'))
      (norm_mul_le_of_le (minor_le_minorSup_02 k) (minor_of_integral_le_one hn 0 2 j j'))
      (norm_mul_le_of_le (minor_le_minorSup_12 k) (minor_of_integral_le_one hn 1 2 j j'))
  exact max_le (max_le (h 0 1) (h 0 2)) (h 1 2)

private theorem lastRowSup_mul_eq {n : GL (Fin 3) L} (hn : IsIntegralUnit3 n) (k : GL (Fin 3) L) :
    lastRowSup (k * n) = lastRowSup k := by
  refine le_antisymm (lastRowSup_mul_le hn.1 k) ?_
  have h := lastRowSup_mul_le hn.2 (k * n)
  rwa [mul_inv_cancel_right] at h

private theorem minorSup_mul_eq {n : GL (Fin 3) L} (hn : IsIntegralUnit3 n) (k : GL (Fin 3) L) :
    minorSup (k * n) = minorSup k := by
  refine le_antisymm (minorSup_mul_le hn.1 k) ?_
  have h := minorSup_mul_le hn.2 (k * n)
  rwa [mul_inv_cancel_right] at h

private theorem detSize_le_one_of_integral {n : GL (Fin 3) L}
    (hn : ∀ i j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) : detSize n ≤ 1 := by
  unfold detSize
  rw [Matrix.det_fin_three]
  have t : ∀ a b c d e f : Fin 3, ‖(n : Matrix (Fin 3) (Fin 3) L) a b *
      (n : Matrix (Fin 3) (Fin 3) L) c d * (n : Matrix (Fin 3) (Fin 3) L) e f‖ ≤ 1 :=
    fun a b c d e f => norm_mul_le_of_le (norm_mul_le_of_le (hn a b) (hn c d)) (hn e f)
  refine (norm_sub_le_max' _ _).trans (max_le ?_ (t _ _ _ _ _ _))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (t _ _ _ _ _ _))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (t _ _ _ _ _ _))
  refine (norm_sub_le_max' _ _).trans (max_le ?_ (t _ _ _ _ _ _))
  exact (norm_sub_le_max' _ _).trans (max_le (t _ _ _ _ _ _) (t _ _ _ _ _ _))

private theorem detSize_eq_one {n : GL (Fin 3) L} (hn : IsIntegralUnit3 n) : detSize n = 1 := by
  have h1 : detSize n * detSize n⁻¹ = 1 := by
    rw [← detSize_mul_eq_mul, mul_inv_cancel]
    simp [detSize]
  have hn1 := detSize_le_one_of_integral hn.1
  have hn2 := detSize_le_one_of_integral hn.2
  refine le_antisymm hn1 ?_
  calc (1 : ℝ) = detSize n * detSize n⁻¹ := h1.symm
    _ ≤ detSize n * 1 := by gcongr; exact norm_nonneg _
    _ = detSize n := mul_one _

end Local

section Adelic

variable {F : Type} [Field F] [NumberField F]

private theorem finRoot₁_mul_of_isIntegralUnit3 (v : HeightOneSpectrum (𝓞 F)) {h : AdelicGL 3 (𝓞 F) F}
    (hh : IsIntegralUnit3 (componentAt3 (𝓞 F) F v h)) (g : AdelicGL 3 (𝓞 F) F) :
    finRoot₁ F v (g * h) = finRoot₁ F v g := by
  simp only [finRoot₁, map_mul, detSize_mul_eq_mul, detSize_eq_one hh, mul_one, lastRowSup_mul_eq hh,
    minorSup_mul_eq hh]

private theorem finRoot₂_mul_of_isIntegralUnit3 (v : HeightOneSpectrum (𝓞 F)) {h : AdelicGL 3 (𝓞 F) F}
    (hh : IsIntegralUnit3 (componentAt3 (𝓞 F) F v h)) (g : AdelicGL 3 (𝓞 F) F) :
    finRoot₂ F v (g * h) = finRoot₂ F v g := by
  simp only [finRoot₂, map_mul, lastRowSup_mul_eq hh, minorSup_mul_eq hh]

end Adelic

end SpanMajorisation.MirabolicMajorantTranslate

end

noncomputable section

namespace SpanMajorisation
namespace MirabolicMajorantBounded

variable {L : Type*} [NormedField L]

private theorem det_ne_zero (k : GL (Fin 3) L) : (k : Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
  have h : (k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one h

private theorem det_eq_minors (k : GL (Fin 3) L) :
    (k : Matrix (Fin 3) (Fin 3) L).det = (k : Matrix (Fin 3) (Fin 3) L) 0 0 * bottomMinor k 1 2 - (k : Matrix
          (Fin 3) (Fin 3) L) 0 1 * bottomMinor k 0 2 +
      (k : Matrix (Fin 3) (Fin 3) L) 0 2 * bottomMinor k 0 1 := by
  rw [Matrix.det_fin_three]
  simp only [bottomMinor]
  ring

private theorem max3_eq_zero {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : max (max x y) z ≤ 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  refine ⟨le_antisymm ?_ hx, le_antisymm ?_ hy, le_antisymm ?_ hz⟩
  · exact ((le_max_left _ _).trans (le_max_left _ _)).trans h
  · exact ((le_max_right _ _).trans (le_max_left _ _)).trans h
  · exact (le_max_right _ _).trans h

private theorem minorSup_pos (k : GL (Fin 3) L) : 0 < minorSup k := by
  by_contra hneg
  obtain ⟨h1, h2, h3⟩ := max3_eq_zero (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (not_lt.mp hneg : minorSup k ≤ 0)
  apply det_ne_zero k
  rw [det_eq_minors, norm_eq_zero.mp h1, norm_eq_zero.mp h2, norm_eq_zero.mp h3]
  ring

private theorem lastRowSup_pos (k : GL (Fin 3) L) : 0 < lastRowSup k := by
  by_contra hneg
  obtain ⟨h1, h2, h3⟩ := max3_eq_zero (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (not_lt.mp hneg : lastRowSup k ≤ 0)
  apply det_ne_zero k
  rw [det_eq_minors]
  simp only [bottomMinor, norm_eq_zero.mp h1, norm_eq_zero.mp h2, norm_eq_zero.mp h3]
  ring

private theorem max3_le_sqrt {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    max (max x y) z ≤ Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
  refine max_le (max_le ?_ ?_) ?_ <;> apply Real.le_sqrt_of_sq_le <;> nlinarith [hx, hy, hz]

private theorem sqrt_le_two_max3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≤ 2 * max (max x y) z := by
  have h1 : x ≤ max (max x y) z := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : y ≤ max (max x y) z := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : z ≤ max (max x y) z := le_max_right _ _
  rw [Real.sqrt_le_iff]
  constructor
  · nlinarith [hx, h1]
  · nlinarith [hx, hy, hz, h1, h2, h3]

private theorem lastRowSup_le_lastRowEucl (k : GL (Fin 3) L) : lastRowSup k ≤ lastRowEucl k :=
  max3_le_sqrt (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

private theorem lastRowEucl_le_two_mul (k : GL (Fin 3) L) : lastRowEucl k ≤ 2 * lastRowSup k :=
  sqrt_le_two_max3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

private theorem minorSup_le_minorEucl (k : GL (Fin 3) L) : minorSup k ≤ minorEucl k :=
  max3_le_sqrt (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

private theorem minorEucl_le_two_mul (k : GL (Fin 3) L) : minorEucl k ≤ 2 * minorSup k :=
  sqrt_le_two_max3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

private theorem lastRowEucl_pos (k : GL (Fin 3) L) : 0 < lastRowEucl k :=
  (lastRowSup_pos k).trans_le (lastRowSup_le_lastRowEucl k)

private theorem minorEucl_pos (k : GL (Fin 3) L) : 0 < minorEucl k :=
  (minorSup_pos k).trans_le (minorSup_le_minorEucl k)

private def entryBound (n : GL (Fin 3) L) : ℝ := 1 + ∑ i, ∑ j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖

private theorem one_le_entryBound (n : GL (Fin 3) L) : 1 ≤ entryBound n := by
  unfold entryBound
  have : 0 ≤ ∑ i, ∑ j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

private theorem norm_entry_le_entryBound (n : GL (Fin 3) L) (a b : Fin 3) : ‖(n : Matrix (Fin 3) (Fin 3) L) a
      b‖ ≤ entryBound n := by
  unfold entryBound
  have h1 : ‖(n : Matrix (Fin 3) (Fin 3) L) a b‖ ≤ ∑ j, ‖(n : Matrix (Fin 3) (Fin 3) L) a j‖ :=
    Finset.single_le_sum (f := fun j => ‖(n : Matrix (Fin 3) (Fin 3) L) a j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ b)
  have h2 : ∑ j, ‖(n : Matrix (Fin 3) (Fin 3) L) a j‖ ≤ ∑ i, ∑ j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖ :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖(n : Matrix (Fin 3) (Fin 3) L) i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  linarith

private theorem entry_mul (k n : GL (Fin 3) L) (i j : Fin 3) :
    ((k * n : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j =
      (k : Matrix (Fin 3) (Fin 3) L) i 0 * (n : Matrix (Fin 3) (Fin 3) L) 0 j + (k : Matrix (Fin 3) (Fin 3) L)
            i 1 * (n : Matrix (Fin 3) (Fin 3) L) 1 j + (k : Matrix (Fin 3) (Fin 3) L) i 2 * (n : Matrix (Fin 3)
            (Fin 3) L) 2 j := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem bottomMinor_mul (k n : GL (Fin 3) L) (j j' : Fin 3) :
    bottomMinor (k * n) j j' =
      bottomMinor k 0 1 * ((n : Matrix (Fin 3) (Fin 3) L) 0 j * (n : Matrix (Fin 3) (Fin 3) L) 1 j' - (n :
            Matrix (Fin 3) (Fin 3) L) 0 j' * (n : Matrix (Fin 3) (Fin 3) L) 1 j) +
        bottomMinor k 0 2 * ((n : Matrix (Fin 3) (Fin 3) L) 0 j * (n : Matrix (Fin 3) (Fin 3) L) 2 j' - (n :
              Matrix (Fin 3) (Fin 3) L) 0 j' * (n : Matrix (Fin 3) (Fin 3) L) 2 j) +
          bottomMinor k 1 2 * ((n : Matrix (Fin 3) (Fin 3) L) 1 j * (n : Matrix (Fin 3) (Fin 3) L) 2 j' - (n :
                Matrix (Fin 3) (Fin 3) L) 1 j' * (n : Matrix (Fin 3) (Fin 3) L) 2 j) := by
  simp only [bottomMinor, entry_mul]
  ring

private theorem norm_comb3_le {a₀ a₁ a₂ b₀ b₁ b₂ : L} {R B : ℝ} (hR : 0 ≤ R)
    (h₀ : ‖a₀‖ ≤ R) (h₁ : ‖a₁‖ ≤ R) (h₂ : ‖a₂‖ ≤ R)
    (g₀ : ‖b₀‖ ≤ B) (g₁ : ‖b₁‖ ≤ B) (g₂ : ‖b₂‖ ≤ B) :
    ‖a₀ * b₀ + a₁ * b₁ + a₂ * b₂‖ ≤ 3 * (R * B) := by
  have t : ∀ {a b : L}, ‖a‖ ≤ R → ‖b‖ ≤ B → ‖a * b‖ ≤ R * B := fun ha hb => by
    rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) hR
  calc ‖a₀ * b₀ + a₁ * b₁ + a₂ * b₂‖ ≤ ‖a₀ * b₀ + a₁ * b₁‖ + ‖a₂ * b₂‖ := norm_add_le _ _
    _ ≤ (‖a₀ * b₀‖ + ‖a₁ * b₁‖) + ‖a₂ * b₂‖ := by
        have := norm_add_le (a₀ * b₀) (a₁ * b₁)
        linarith
    _ ≤ (R * B + R * B) + R * B := add_le_add (add_le_add (t h₀ g₀) (t h₁ g₁)) (t h₂ g₂)
    _ = 3 * (R * B) := by ring

private theorem entry_le_lastRowSup (k : GL (Fin 3) L) (j : Fin 3) : ‖(k : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤
      lastRowSup k := by
  unfold lastRowSup
  fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem norm_minor_of_entries_le (n : GL (Fin 3) L) (a b j j' : Fin 3) :
    ‖(n : Matrix (Fin 3) (Fin 3) L) a j * (n : Matrix (Fin 3) (Fin 3) L) b j' - (n : Matrix (Fin 3) (Fin 3) L)
          a j' * (n : Matrix (Fin 3) (Fin 3) L) b j‖ ≤ 2 * entryBound n ^ 2 := by
  have e := norm_entry_le_entryBound n
  have h0 : (0 : ℝ) ≤ entryBound n := zero_le_one.trans (one_le_entryBound n)
  calc ‖(n : Matrix (Fin 3) (Fin 3) L) a j * (n : Matrix (Fin 3) (Fin 3) L) b j' - (n : Matrix (Fin 3) (Fin 3)
        L) a j' * (n : Matrix (Fin 3) (Fin 3) L) b j‖
      ≤ ‖(n : Matrix (Fin 3) (Fin 3) L) a j * (n : Matrix (Fin 3) (Fin 3) L) b j'‖ + ‖(n : Matrix (Fin 3) (Fin
            3) L) a j' * (n : Matrix (Fin 3) (Fin 3) L) b j‖ := norm_sub_le _ _
    _ = ‖(n : Matrix (Fin 3) (Fin 3) L) a j‖ * ‖(n : Matrix (Fin 3) (Fin 3) L) b j'‖ + ‖(n : Matrix (Fin 3)
          (Fin 3) L) a j'‖ * ‖(n : Matrix (Fin 3) (Fin 3) L) b j‖ := by rw [norm_mul, norm_mul]
    _ ≤ entryBound n * entryBound n + entryBound n * entryBound n := by
        gcongr <;> exact e _ _
    _ = 2 * entryBound n ^ 2 := by ring

private theorem lastRowSup_mul_le_bound (k n : GL (Fin 3) L) :
    lastRowSup (k * n) ≤ 3 * (lastRowSup k * entryBound n) := by
  have h : ∀ j, ‖((k * n : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ 3 * (lastRowSup k * entryBound n) := by
    intro j
    rw [entry_mul]
    exact norm_comb3_le (lastRowSup_pos k).le (entry_le_lastRowSup k 0) (entry_le_lastRowSup k 1)
      (entry_le_lastRowSup k 2) (norm_entry_le_entryBound n 0 j) (norm_entry_le_entryBound n 1 j)
      (norm_entry_le_entryBound n 2 j)
  exact max_le (max_le (h 0) (h 1)) (h 2)

private theorem minorSup_mul_le_bound (k n : GL (Fin 3) L) :
    minorSup (k * n) ≤ 3 * (minorSup k * (2 * entryBound n ^ 2)) := by
  have m01 : ‖bottomMinor k 0 1‖ ≤ minorSup k := (le_max_left _ _).trans (le_max_left _ _)
  have m02 : ‖bottomMinor k 0 2‖ ≤ minorSup k := (le_max_right _ _).trans (le_max_left _ _)
  have m12 : ‖bottomMinor k 1 2‖ ≤ minorSup k := le_max_right _ _
  have h : ∀ j j', ‖bottomMinor (k * n) j j'‖ ≤ 3 * (minorSup k * (2 * entryBound n ^ 2)) := by
    intro j j'
    rw [bottomMinor_mul]
    exact norm_comb3_le (minorSup_pos k).le m01 m02 m12 (norm_minor_of_entries_le n 0 1 j j')
      (norm_minor_of_entries_le n 0 2 j j') (norm_minor_of_entries_le n 1 2 j j')
  exact max_le (max_le (h 0 1) (h 0 2)) (h 1 2)

private theorem detSize_mul' (k n : GL (Fin 3) L) : detSize (k * n) = detSize k * detSize n := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, norm_mul]

private def translateConst (n : GL (Fin 3) L) : ℝ :=
  108 * entryBound (n⁻¹) * entryBound n ^ 4 * (1 + detSize (n⁻¹)) +
    54 * entryBound (n⁻¹) ^ 2 * entryBound n ^ 2

private theorem one_le_translateConst (n : GL (Fin 3) L) : 1 ≤ translateConst n := by
  unfold translateConst
  have h1 := one_le_entryBound n
  have h2 := one_le_entryBound (n⁻¹)
  have h3 : (0 : ℝ) ≤ detSize (n⁻¹) := norm_nonneg _
  have h1' : (0 : ℝ) ≤ entryBound n := zero_le_one.trans h1
  have h2' : (0 : ℝ) ≤ entryBound (n⁻¹) := zero_le_one.trans h2
  have hA : (0 : ℝ) ≤ 108 * entryBound (n⁻¹) * entryBound n ^ 4 * (1 + detSize (n⁻¹)) := by positivity
  have hB : (1 : ℝ) ≤ entryBound (n⁻¹) ^ 2 * entryBound n ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ h2) (one_le_pow₀ h1)
  nlinarith [hA, hB]

private theorem size_bounds (k n : GL (Fin 3) L) :
    detSize k = detSize (k * n) * detSize (n⁻¹) ∧
      lastRowSup k ≤ 3 * (lastRowSup (k * n) * entryBound (n⁻¹)) ∧
        minorSup (k * n) ≤ 3 * (minorSup k * (2 * entryBound n ^ 2)) ∧
          lastRowSup (k * n) ≤ 3 * (lastRowSup k * entryBound n) ∧
            minorSup k ≤ 3 * (minorSup (k * n) * (2 * entryBound (n⁻¹) ^ 2)) := by
  refine ⟨?_, ?_, minorSup_mul_le_bound k n, lastRowSup_mul_le_bound k n, ?_⟩
  · rw [← detSize_mul', mul_inv_cancel_right]
  · have h := lastRowSup_mul_le_bound (k * n) (n⁻¹)
    rwa [mul_inv_cancel_right] at h
  · have h := minorSup_mul_le_bound (k * n) (n⁻¹)
    rwa [mul_inv_cancel_right] at h

private theorem root₁_sup_le (k n : GL (Fin 3) L) :
    detSize k * lastRowSup k / minorSup k ^ 2 ≤
      translateConst n * (detSize (k * n) * lastRowSup (k * n) / minorSup (k * n) ^ 2) := by
  obtain ⟨hd, hr, hm, -, -⟩ := size_bounds k n
  have pk := minorSup_pos k
  have pkn := minorSup_pos (k * n)
  have rkn := (lastRowSup_pos (k * n)).le
  have d1 : (0 : ℝ) ≤ detSize (k * n) := norm_nonneg _
  have d2 : (0 : ℝ) ≤ detSize (n⁻¹) := norm_nonneg _
  have e1 : (0 : ℝ) ≤ entryBound n := zero_le_one.trans (one_le_entryBound n)
  have e2 : (0 : ℝ) ≤ entryBound (n⁻¹) := zero_le_one.trans (one_le_entryBound (n⁻¹))
  have hκ : 108 * entryBound (n⁻¹) * entryBound n ^ 4 * detSize (n⁻¹) ≤ translateConst n := by
    unfold translateConst
    have hA : (0 : ℝ) ≤ 108 * entryBound (n⁻¹) * entryBound n ^ 4 := by positivity
    have hB : (0 : ℝ) ≤ 54 * entryBound (n⁻¹) ^ 2 * entryBound n ^ 2 := by positivity
    nlinarith [hA, hB]
  have hratio : 0 ≤ detSize (k * n) * lastRowSup (k * n) / minorSup (k * n) ^ 2 := by positivity
  calc detSize k * lastRowSup k / minorSup k ^ 2
      ≤ (108 * entryBound (n⁻¹) * entryBound n ^ 4 * detSize (n⁻¹)) *
          (detSize (k * n) * lastRowSup (k * n) / minorSup (k * n) ^ 2) := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), hd]
        calc detSize (k * n) * detSize (n⁻¹) * lastRowSup k * minorSup (k * n) ^ 2
            ≤ detSize (k * n) * detSize (n⁻¹) * (3 * (lastRowSup (k * n) * entryBound (n⁻¹))) *
                (3 * (minorSup k * (2 * entryBound n ^ 2))) ^ 2 := by gcongr
          _ = 108 * entryBound (n⁻¹) * entryBound n ^ 4 * detSize (n⁻¹) *
                (detSize (k * n) * lastRowSup (k * n)) * minorSup k ^ 2 := by ring
    _ ≤ translateConst n * (detSize (k * n) * lastRowSup (k * n) / minorSup (k * n) ^ 2) :=
        mul_le_mul_of_nonneg_right hκ hratio

private theorem root₂_sup_le (k n : GL (Fin 3) L) :
    minorSup k / lastRowSup k ^ 2 ≤ translateConst n * (minorSup (k * n) / lastRowSup (k * n) ^ 2) := by
  obtain ⟨-, -, -, hr', hm'⟩ := size_bounds k n
  have pk := lastRowSup_pos k
  have pkn := lastRowSup_pos (k * n)
  have mkn := (minorSup_pos (k * n)).le
  have e1 : (0 : ℝ) ≤ entryBound n := zero_le_one.trans (one_le_entryBound n)
  have e2 : (0 : ℝ) ≤ entryBound (n⁻¹) := zero_le_one.trans (one_le_entryBound (n⁻¹))
  have d2 : (0 : ℝ) ≤ detSize (n⁻¹) := norm_nonneg _
  have hκ : 54 * entryBound (n⁻¹) ^ 2 * entryBound n ^ 2 ≤ translateConst n := by
    unfold translateConst
    have h4 : (0 : ℝ) ≤ 108 * entryBound (n⁻¹) * entryBound n ^ 4 * (1 + detSize (n⁻¹)) := by
      positivity
    linarith
  have hratio : 0 ≤ minorSup (k * n) / lastRowSup (k * n) ^ 2 := by positivity
  calc minorSup k / lastRowSup k ^ 2
      ≤ (54 * entryBound (n⁻¹) ^ 2 * entryBound n ^ 2) * (minorSup (k * n) / lastRowSup (k * n) ^ 2) := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
        calc minorSup k * lastRowSup (k * n) ^ 2
            ≤ (3 * (minorSup (k * n) * (2 * entryBound (n⁻¹) ^ 2))) *
                (3 * (lastRowSup k * entryBound n)) ^ 2 := by gcongr
          _ = 54 * entryBound (n⁻¹) ^ 2 * entryBound n ^ 2 * minorSup (k * n) * lastRowSup k ^ 2 := by
              ring
    _ ≤ translateConst n * (minorSup (k * n) / lastRowSup (k * n) ^ 2) :=
        mul_le_mul_of_nonneg_right hκ hratio

private theorem root₁_eucl_le (k n : GL (Fin 3) L) :
    detSize k * lastRowEucl k / minorEucl k ^ 2 ≤
      8 * translateConst n * (detSize (k * n) * lastRowEucl (k * n) / minorEucl (k * n) ^ 2) := by
  have e1 := lastRowEucl_le_two_mul k
  have e2 := minorSup_le_minorEucl k
  have e3 := lastRowSup_le_lastRowEucl (k * n)
  have e4 := minorEucl_le_two_mul (k * n)
  have p1 := minorSup_pos k
  have p2 := minorEucl_pos k
  have p3 := minorSup_pos (k * n)
  have p4 := minorEucl_pos (k * n)
  have d0 : 0 ≤ detSize k := norm_nonneg _
  have d1 : 0 ≤ detSize (k * n) := norm_nonneg _
  have r0 := (lastRowSup_pos k).le
  have r1 := (lastRowEucl_pos (k * n)).le
  have r2 := (lastRowSup_pos (k * n)).le
  have hκ := one_le_translateConst n
  have s1 : detSize k * lastRowEucl k / minorEucl k ^ 2 ≤ 2 * (detSize k * lastRowSup k / minorSup k ^ 2) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc detSize k * lastRowEucl k * minorSup k ^ 2
        ≤ detSize k * (2 * lastRowSup k) * minorEucl k ^ 2 := by gcongr
      _ = 2 * (detSize k * lastRowSup k) * minorEucl k ^ 2 := by ring
  have s2 : detSize (k * n) * lastRowSup (k * n) / minorSup (k * n) ^ 2 ≤
      4 * (detSize (k * n) * lastRowEucl (k * n) / minorEucl (k * n) ^ 2) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc detSize (k * n) * lastRowSup (k * n) * minorEucl (k * n) ^ 2
        ≤ detSize (k * n) * lastRowEucl (k * n) * (2 * minorSup (k * n)) ^ 2 := by gcongr
      _ = 4 * (detSize (k * n) * lastRowEucl (k * n)) * minorSup (k * n) ^ 2 := by ring
  have h := root₁_sup_le k n
  have hκ0 : 0 ≤ translateConst n := zero_le_one.trans hκ
  calc detSize k * lastRowEucl k / minorEucl k ^ 2
      ≤ 2 * (detSize k * lastRowSup k / minorSup k ^ 2) := s1
    _ ≤ 2 * (translateConst n * (detSize (k * n) * lastRowSup (k * n) / minorSup (k * n) ^ 2)) := by
        gcongr
    _ ≤ 2 * (translateConst n * (4 * (detSize (k * n) * lastRowEucl (k * n) / minorEucl (k * n) ^ 2))) := by
        gcongr
    _ = 8 * translateConst n * (detSize (k * n) * lastRowEucl (k * n) / minorEucl (k * n) ^ 2) := by ring

private theorem root₂_eucl_le (k n : GL (Fin 3) L) :
    minorEucl k / lastRowEucl k ^ 2 ≤ 8 * translateConst n * (minorEucl (k * n) / lastRowEucl (k * n) ^ 2) := by
  have e1 := minorEucl_le_two_mul k
  have e2 := lastRowSup_le_lastRowEucl k
  have e3 := minorSup_le_minorEucl (k * n)
  have e4 := lastRowEucl_le_two_mul (k * n)
  have p1 := lastRowSup_pos k
  have p2 := lastRowEucl_pos k
  have p3 := lastRowSup_pos (k * n)
  have p4 := lastRowEucl_pos (k * n)
  have m0 : 0 ≤ minorEucl k := (minorEucl_pos k).le
  have m1 : 0 ≤ minorSup (k * n) := (minorSup_pos (k * n)).le
  have m2 : 0 ≤ minorSup k := (minorSup_pos k).le
  have m3 : 0 ≤ minorEucl (k * n) := (minorEucl_pos (k * n)).le
  have hκ := one_le_translateConst n
  have s1 : minorEucl k / lastRowEucl k ^ 2 ≤ 2 * (minorSup k / lastRowSup k ^ 2) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc minorEucl k * lastRowSup k ^ 2 ≤ (2 * minorSup k) * lastRowEucl k ^ 2 := by gcongr
      _ = 2 * minorSup k * lastRowEucl k ^ 2 := by ring
  have s2 : minorSup (k * n) / lastRowSup (k * n) ^ 2 ≤ 4 * (minorEucl (k * n) / lastRowEucl (k * n) ^ 2) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc minorSup (k * n) * lastRowEucl (k * n) ^ 2
        ≤ minorEucl (k * n) * (2 * lastRowSup (k * n)) ^ 2 := by gcongr
      _ = 4 * minorEucl (k * n) * lastRowSup (k * n) ^ 2 := by ring
  have h := root₂_sup_le k n
  have hκ0 : 0 ≤ translateConst n := zero_le_one.trans hκ
  calc minorEucl k / lastRowEucl k ^ 2 ≤ 2 * (minorSup k / lastRowSup k ^ 2) := s1
    _ ≤ 2 * (translateConst n * (minorSup (k * n) / lastRowSup (k * n) ^ 2)) := by gcongr
    _ ≤ 2 * (translateConst n * (4 * (minorEucl (k * n) / lastRowEucl (k * n) ^ 2))) := by gcongr
    _ = 8 * translateConst n * (minorEucl (k * n) / lastRowEucl (k * n) ^ 2) := by ring

end SpanMajorisation.MirabolicMajorantBounded

end

noncomputable section

namespace SpanMajorisation

open MirabolicMajorantSupport MirabolicMajorantTranslate MirabolicMajorantBounded

namespace MirabolicMajorantRightTranslate

section Generic

variable {L : Type*} [NormedField L]

private theorem detSize_pos (k : GL (Fin 3) L) : 0 < detSize k := by
  unfold detSize
  rw [norm_pos_iff]
  have h : (k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one h

end Generic

variable {F : Type} [Field F] [NumberField F]

private theorem finRoot₁_pos (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) : 0 < finRoot₁ F v g :=
  div_pos (mul_pos (detSize_pos _) (lastRowSup_pos _)) (pow_pos (minorSup_pos _) 2)

private theorem finRoot₂_pos (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) : 0 < finRoot₂ F v g :=
  div_pos (minorSup_pos _) (pow_pos (lastRowSup_pos _) 2)

private theorem archRoot₁_pos (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : 0 < archRoot₁ F w g :=
  div_pos (mul_pos (detSize_pos _) (lastRowEucl_pos _)) (pow_pos (minorEucl_pos _) 2)

private theorem archRoot₂_pos (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : 0 < archRoot₂ F w g :=
  div_pos (minorEucl_pos _) (pow_pos (lastRowEucl_pos _) 2)

private theorem archRootSum_nonneg (g : AdelicGL 3 (𝓞 F) F) : 0 ≤ archRootSum F g :=
  Finset.sum_nonneg fun w _ => add_nonneg (archRoot₁_pos w g).le (archRoot₂_pos w g).le

private theorem finFactor_eq_prod (g : AdelicGL 3 (𝓞 F) F) {U : Finset (HeightOneSpectrum (𝓞 F))}
    (hU : (mulSupport_finRootProd_finite F g).toFinset ⊆ U) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), finRoot₁ F v g * finRoot₂ F v g) =
      ∏ v ∈ U, finRoot₁ F v g * finRoot₂ F v g := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  exact hU ((mulSupport_finRootProd_finite F g).mem_toFinset.mpr hv)

private theorem rootSizeProd_pos (g : AdelicGL 3 (𝓞 F) F) : 0 < rootSizeProd F g := by
  unfold rootSizeProd
  rw [finFactor_eq_prod g (Finset.Subset.refl _)]
  exact mul_pos (Finset.prod_pos fun v _ => mul_pos (finRoot₁_pos v g) (finRoot₂_pos v g))
    (Finset.prod_pos fun w _ => mul_pos (archRoot₁_pos w g) (archRoot₂_pos w g))

private def finConst (h : AdelicGL 3 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  translateConst (componentAt3 (𝓞 F) F v h)

private def archConst (h : AdelicGL 3 (𝓞 F) F) (w : InfinitePlace F) : ℝ :=
  8 * translateConst (archPlaceComponent3 F w h)

private theorem one_le_finConst (h : AdelicGL 3 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : 1 ≤ finConst h v :=
  one_le_translateConst _

private theorem one_le_archConst (h : AdelicGL 3 (𝓞 F) F) (w : InfinitePlace F) : 1 ≤ archConst h w := by
  unfold archConst
  have := one_le_translateConst (archPlaceComponent3 F w h)
  linarith

private theorem finRoot₁_le_mul (h g : AdelicGL 3 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finRoot₁ F v g ≤ finConst h v * finRoot₁ F v (g * h) := by
  unfold finRoot₁ finConst
  rw [map_mul]
  exact root₁_sup_le _ _

private theorem finRoot₂_le_mul (h g : AdelicGL 3 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finRoot₂ F v g ≤ finConst h v * finRoot₂ F v (g * h) := by
  unfold finRoot₂ finConst
  rw [map_mul]
  exact root₂_sup_le _ _

private theorem archRoot₁_le_mul (h g : AdelicGL 3 (𝓞 F) F) (w : InfinitePlace F) :
    archRoot₁ F w g ≤ archConst h w * archRoot₁ F w (g * h) := by
  unfold archRoot₁ archConst
  rw [map_mul]
  exact root₁_eucl_le _ _

private theorem archRoot₂_le_mul (h g : AdelicGL 3 (𝓞 F) F) (w : InfinitePlace F) :
    archRoot₂ F w g ≤ archConst h w * archRoot₂ F w (g * h) := by
  unfold archRoot₂ archConst
  rw [map_mul]
  exact root₂_eucl_le _ _

private theorem norm_le_one_of_valued_le_one {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F}
    (hx : Valued.v x ≤ 1) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.2 hx

private theorem exists_badSet (h : AdelicGL 3 (𝓞 F) F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ v, v ∉ S → IsIntegralUnit3 (componentAt3 (𝓞 F) F v h) := by
  have e : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      IsIntegralUnit3 (componentAt3 (𝓞 F) F v h) := by
    filter_upwards [eventually_integral_componentAt3 F h, eventually_integral_componentAt3 F h⁻¹]
      with v h₁ h₂
    refine ⟨fun i j => norm_le_one_of_valued_le_one (h₁.1 i j), fun i j => ?_⟩
    have h₂' := h₂.1 i j
    rw [map_inv] at h₂'
    exact norm_le_one_of_valued_le_one h₂'
  have hfin := Filter.eventually_cofinite.mp e
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  by_contra hcon
  exact hv (hfin.mem_toFinset.mpr hcon)

open Classical in
private theorem inRootLevel_of_mul {h : AdelicGL 3 (𝓞 F) F} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v, v ∉ S → IsIntegralUnit3 (componentAt3 (𝓞 F) F v h)) {K : ℝ} (hK1 : 1 ≤ K)
    (hKS : ∀ v ∈ S, finConst h v ≤ K) {T : Finset (HeightOneSpectrum (𝓞 F))} {B : ℝ}
    {g : AdelicGL 3 (𝓞 F) F} (hg : InRootLevel F T B (g * h)) :
    InRootLevel F (T ∪ S) (K * max B 1) g := by
  obtain ⟨hout, hin⟩ := hg
  have hmax : ∀ v, finRoot₁ F v (g * h) ≤ max B 1 ∧ finRoot₂ F v (g * h) ≤ max B 1 := by
    intro v
    by_cases hv : v ∈ T
    · exact ⟨(hin v hv).1.trans (le_max_left _ _), (hin v hv).2.trans (le_max_left _ _)⟩
    · exact ⟨(hout v hv).1.trans (le_max_right _ _), (hout v hv).2.trans (le_max_right _ _)⟩
  have hm0 : (0 : ℝ) ≤ max B 1 := zero_le_one.trans (le_max_right _ _)
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK1
  refine ⟨fun v hv => ?_, fun v _ => ?_⟩
  · rw [Finset.mem_union, not_or] at hv
    rw [← finRoot₁_mul_of_isIntegralUnit3 v (hS v hv.2) g, ← finRoot₂_mul_of_isIntegralUnit3 v (hS v hv.2) g]
    exact hout v hv.1
  · by_cases hvS : v ∈ S
    · exact ⟨(finRoot₁_le_mul h g v).trans
          (mul_le_mul (hKS v hvS) (hmax v).1 (finRoot₁_pos v _).le hK0),
        (finRoot₂_le_mul h g v).trans (mul_le_mul (hKS v hvS) (hmax v).2 (finRoot₂_pos v _).le hK0)⟩
    · rw [← finRoot₁_mul_of_isIntegralUnit3 v (hS v hvS) g, ← finRoot₂_mul_of_isIntegralUnit3 v (hS v hvS) g]
      exact ⟨(hmax v).1.trans (le_mul_of_one_le_left hm0 hK1), (hmax v).2.trans (le_mul_of_one_le_left hm0 hK1)⟩

private def prodConst (h : AdelicGL 3 (𝓞 F) F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ :=
  (∏ v ∈ S, finConst h v ^ 2) * ∏ w : InfinitePlace F, archConst h w ^ 2

private theorem prodConst_nonneg (h : AdelicGL 3 (𝓞 F) F) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    0 ≤ prodConst h S :=
  mul_nonneg (Finset.prod_nonneg fun v _ => pow_nonneg (zero_le_one.trans (one_le_finConst h v)) 2)
    (Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (one_le_archConst h w)) 2)

private theorem rootSizeProd_le_mul {h : AdelicGL 3 (𝓞 F) F} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v, v ∉ S → IsIntegralUnit3 (componentAt3 (𝓞 F) F v h)) (g : AdelicGL 3 (𝓞 F) F) :
    rootSizeProd F g ≤ prodConst h S * rootSizeProd F (g * h) := by
  classical
  set U : Finset (HeightOneSpectrum (𝓞 F)) :=
    S ∪ (mulSupport_finRootProd_finite F g).toFinset ∪
      (mulSupport_finRootProd_finite F (g * h)).toFinset with hU
  have hSU : S ⊆ U := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hgU : (mulSupport_finRootProd_finite F g).toFinset ⊆ U :=
    fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hghU : (mulSupport_finRootProd_finite F (g * h)).toFinset ⊆ U :=
    fun v hv => Finset.mem_union_right _ hv
  unfold rootSizeProd
  rw [finFactor_eq_prod g hgU, finFactor_eq_prod (g * h) hghU]
  have hfin : (∏ v ∈ U, finRoot₁ F v g * finRoot₂ F v g) ≤
      (∏ v ∈ S, finConst h v ^ 2) * ∏ v ∈ U, finRoot₁ F v (g * h) * finRoot₂ F v (g * h) := by
    calc (∏ v ∈ U, finRoot₁ F v g * finRoot₂ F v g)
        ≤ ∏ v ∈ U, (if v ∈ S then finConst h v ^ 2 else 1) *
            (finRoot₁ F v (g * h) * finRoot₂ F v (g * h)) := by
          apply Finset.prod_le_prod
          · intro v _
            exact mul_nonneg (finRoot₁_pos v g).le (finRoot₂_pos v g).le
          · intro v _
            by_cases hvS : v ∈ S
            · rw [if_pos hvS]
              have h1 := finRoot₁_le_mul h g v
              have h2 := finRoot₂_le_mul h g v
              calc finRoot₁ F v g * finRoot₂ F v g
                  ≤ (finConst h v * finRoot₁ F v (g * h)) * (finConst h v * finRoot₂ F v (g * h)) :=
                    mul_le_mul h1 h2 (finRoot₂_pos v g).le
                      (mul_nonneg (zero_le_one.trans (one_le_finConst h v)) (finRoot₁_pos v _).le)
                _ = finConst h v ^ 2 * (finRoot₁ F v (g * h) * finRoot₂ F v (g * h)) := by ring
            · rw [if_neg hvS, one_mul, finRoot₁_mul_of_isIntegralUnit3 v (hS v hvS) g,
                finRoot₂_mul_of_isIntegralUnit3 v (hS v hvS) g]
      _ = (∏ v ∈ U, if v ∈ S then finConst h v ^ 2 else 1) *
            ∏ v ∈ U, finRoot₁ F v (g * h) * finRoot₂ F v (g * h) := Finset.prod_mul_distrib
      _ = (∏ v ∈ S, finConst h v ^ 2) * ∏ v ∈ U, finRoot₁ F v (g * h) * finRoot₂ F v (g * h) := by
          rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hSU]
  have harch : (∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g) ≤
      (∏ w : InfinitePlace F, archConst h w ^ 2) *
        ∏ w : InfinitePlace F, archRoot₁ F w (g * h) * archRoot₂ F w (g * h) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro w _
      exact mul_nonneg (archRoot₁_pos w g).le (archRoot₂_pos w g).le
    · intro w _
      calc archRoot₁ F w g * archRoot₂ F w g
          ≤ (archConst h w * archRoot₁ F w (g * h)) * (archConst h w * archRoot₂ F w (g * h)) :=
            mul_le_mul (archRoot₁_le_mul h g w) (archRoot₂_le_mul h g w) (archRoot₂_pos w g).le
              (mul_nonneg (zero_le_one.trans (one_le_archConst h w)) (archRoot₁_pos w _).le)
        _ = archConst h w ^ 2 * (archRoot₁ F w (g * h) * archRoot₂ F w (g * h)) := by ring
  have hA0 : 0 ≤ ∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g :=
    Finset.prod_nonneg fun w _ => mul_nonneg (archRoot₁_pos w g).le (archRoot₂_pos w g).le
  have hF0 : 0 ≤ (∏ v ∈ S, finConst h v ^ 2) * ∏ v ∈ U, finRoot₁ F v (g * h) * finRoot₂ F v (g * h) :=
    mul_nonneg (Finset.prod_nonneg fun v _ => pow_nonneg (zero_le_one.trans (one_le_finConst h v)) 2)
      (Finset.prod_nonneg fun v _ => mul_nonneg (finRoot₁_pos v _).le (finRoot₂_pos v _).le)
  calc (∏ v ∈ U, finRoot₁ F v g * finRoot₂ F v g) * ∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g
      ≤ ((∏ v ∈ S, finConst h v ^ 2) * ∏ v ∈ U, finRoot₁ F v (g * h) * finRoot₂ F v (g * h)) *
          ((∏ w : InfinitePlace F, archConst h w ^ 2) *
            ∏ w : InfinitePlace F, archRoot₁ F w (g * h) * archRoot₂ F w (g * h)) :=
        mul_le_mul hfin harch hA0 hF0
    _ = prodConst h S * ((∏ v ∈ U, finRoot₁ F v (g * h) * finRoot₂ F v (g * h)) *
          ∏ w : InfinitePlace F, archRoot₁ F w (g * h) * archRoot₂ F w (g * h)) := by
        unfold prodConst
        ring

private def sumConst (h : AdelicGL 3 (𝓞 F) F) : ℝ := 1 + ∑ w : InfinitePlace F, archConst h w

private theorem one_le_sumConst (h : AdelicGL 3 (𝓞 F) F) : 1 ≤ sumConst h := by
  unfold sumConst
  have : 0 ≤ ∑ w : InfinitePlace F, archConst h w :=
    Finset.sum_nonneg fun w _ => zero_le_one.trans (one_le_archConst h w)
  linarith

private theorem archConst_le_sumConst (h : AdelicGL 3 (𝓞 F) F) (w : InfinitePlace F) : archConst h w ≤ sumConst h := by
  unfold sumConst
  have : archConst h w ≤ ∑ w : InfinitePlace F, archConst h w :=
    Finset.single_le_sum (f := fun w => archConst h w)
      (fun w _ => zero_le_one.trans (one_le_archConst h w)) (Finset.mem_univ w)
  linarith

private theorem archRootSum_le_mul (h g : AdelicGL 3 (𝓞 F) F) :
    archRootSum F g ≤ sumConst h * archRootSum F (g * h) := by
  unfold archRootSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  have hw0 : 0 ≤ archRoot₁ F w (g * h) + archRoot₂ F w (g * h) :=
    add_nonneg (archRoot₁_pos w _).le (archRoot₂_pos w _).le
  calc archRoot₁ F w g + archRoot₂ F w g
      ≤ archConst h w * archRoot₁ F w (g * h) + archConst h w * archRoot₂ F w (g * h) :=
        add_le_add (archRoot₁_le_mul h g w) (archRoot₂_le_mul h g w)
    _ = archConst h w * (archRoot₁ F w (g * h) + archRoot₂ F w (g * h)) := by ring
    _ ≤ sumConst h * (archRoot₁ F w (g * h) + archRoot₂ F w (g * h)) :=
        mul_le_mul_of_nonneg_right (archConst_le_sumConst h w) hw0

private theorem one_add_archRootSum_le_mul (h g : AdelicGL 3 (𝓞 F) F) :
    1 + archRootSum F g ≤ sumConst h * (1 + archRootSum F (g * h)) := by
  have h1 := archRootSum_le_mul h g
  have h2 := one_le_sumConst h
  rw [mul_add, mul_one]
  linarith

private theorem isGaugeMajorised3_mul_right {W : AdelicGL 3 (𝓞 F) F → ℂ} (hW : IsGaugeMajorised3 F W)
    (h : AdelicGL 3 (𝓞 F) F) : IsGaugeMajorised3 F fun g => W (g * h) := by
  classical
  obtain ⟨t, T, B, hW⟩ := hW
  obtain ⟨S, hS⟩ := exists_badSet h
  set K : ℝ := 1 + ∑ v ∈ S, finConst h v with hKdef
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ v ∈ S, finConst h v :=
      Finset.sum_nonneg fun v _ => zero_le_one.trans (one_le_finConst h v)
    rw [hKdef]
    linarith
  have hKS : ∀ v ∈ S, finConst h v ≤ K := by
    intro v hv
    have : finConst h v ≤ ∑ v ∈ S, finConst h v :=
      Finset.single_le_sum (f := fun v => finConst h v)
        (fun v _ => zero_le_one.trans (one_le_finConst h v)) hv
    rw [hKdef]
    linarith
  refine ⟨t, T ∪ S, K * max B 1, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hW N
  have hP0 := prodConst_nonneg h S
  have hA1 := one_le_sumConst h
  have hnum : 0 ≤ max C 0 * (prodConst h S ^ t * sumConst h ^ N) := by
    have : (0 : ℝ) ≤ sumConst h := zero_le_one.trans hA1
    positivity
  refine ⟨max C 0 * (prodConst h S ^ t * sumConst h ^ N), fun g => ⟨fun hbox => ?_, fun _ => ?_⟩⟩
  ·
    show W (g * h) = 0
    by_contra hne
    have hgh : InRootLevel F T B (g * h) := by
      by_contra hnot
      exact hne ((hC (g * h)).1 hnot)
    exact hbox (inRootLevel_of_mul hS hK1 hKS hgh)
  ·
    show ‖W (g * h)‖ ≤ _
    have hden : 0 < rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N := by
      have := rootSizeProd_pos g
      have := archRootSum_nonneg g
      positivity
    by_cases hgh : InRootLevel F T B (g * h)
    · have hbound := (hC (g * h)).2 hgh
      have hden' : 0 < rootSizeProd F (g * h) ^ t * (1 + archRootSum F (g * h)) ^ N := by
        have := rootSizeProd_pos (g * h)
        have := archRootSum_nonneg (g * h)
        positivity
      have hKt : 0 < prodConst h S ^ t * sumConst h ^ N := by
        have hPpos : 0 < prodConst h S := by
          unfold prodConst
          exact mul_pos (Finset.prod_pos fun v _ => pow_pos (zero_lt_one.trans_le (one_le_finConst h v)) 2)
            (Finset.prod_pos fun w _ => pow_pos (zero_lt_one.trans_le (one_le_archConst h w)) 2)
        have : (0 : ℝ) < sumConst h := zero_lt_one.trans_le hA1
        positivity
      have hcmp : rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N ≤
          (rootSizeProd F (g * h) ^ t * (1 + archRootSum F (g * h)) ^ N) *
            (prodConst h S ^ t * sumConst h ^ N) := by
        have e1 : rootSizeProd F g ^ t ≤ (prodConst h S * rootSizeProd F (g * h)) ^ t :=
          pow_le_pow_left₀ (rootSizeProd_pos g).le (rootSizeProd_le_mul hS g) t
        have e2 : (1 + archRootSum F g) ^ N ≤ (sumConst h * (1 + archRootSum F (g * h))) ^ N :=
          pow_le_pow_left₀ (by have := archRootSum_nonneg g; linarith) (one_add_archRootSum_le_mul h g) N
        calc rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N
            ≤ (prodConst h S * rootSizeProd F (g * h)) ^ t * (sumConst h * (1 + archRootSum F (g * h))) ^ N :=
              mul_le_mul e1 e2 (pow_nonneg (by have := archRootSum_nonneg g; linarith) N) (pow_nonneg
                (mul_nonneg hP0 (rootSizeProd_pos (g * h)).le) t)
          _ = (rootSizeProd F (g * h) ^ t * (1 + archRootSum F (g * h)) ^ N) *
                (prodConst h S ^ t * sumConst h ^ N) := by
              rw [mul_pow, mul_pow]
              ring
      calc ‖W (g * h)‖ ≤ C / (rootSizeProd F (g * h) ^ t * (1 + archRootSum F (g * h)) ^ N) := hbound
        _ ≤ max C 0 / (rootSizeProd F (g * h) ^ t * (1 + archRootSum F (g * h)) ^ N) :=
            div_le_div_of_nonneg_right (le_max_left _ _) hden'.le
        _ = max C 0 * (prodConst h S ^ t * sumConst h ^ N) /
              ((rootSizeProd F (g * h) ^ t * (1 + archRootSum F (g * h)) ^ N) *
                (prodConst h S ^ t * sumConst h ^ N)) :=
            (mul_div_mul_right _ _ hKt.ne').symm
        _ ≤ max C 0 * (prodConst h S ^ t * sumConst h ^ N) /
              (rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N) :=
            div_le_div_of_nonneg_left hnum hden hcmp
    · rw [(hC (g * h)).1 hgh, norm_zero]
      exact div_nonneg hnum hden.le

end MirabolicMajorantRightTranslate

end SpanMajorisation

end

namespace SpanMajorisation
namespace MirabolicMajorantClosure

variable {F : Type} [Field F] [NumberField F]

private theorem isGaugeMajorised3_const_mul (c : ℂ) {W : AdelicGL 3 (𝓞 F) F → ℂ}
    (hW : IsGaugeMajorised3 F W) : IsGaugeMajorised3 F (fun g => c * W g) := by
  obtain ⟨t, T, B, h⟩ := hW
  refine ⟨t, T, B, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h N
  refine ⟨‖c‖ * C, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · simp only [(hC g).1 hg, mul_zero]
  · calc ‖c * W g‖ = ‖c‖ * ‖W g‖ := norm_mul _ _
      _ ≤ ‖c‖ * (C / (rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N)) := by
          gcongr; exact (hC g).2 hg
      _ = ‖c‖ * C / (rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N) := (mul_div_assoc _ _ _).symm

end SpanMajorisation.MirabolicMajorantClosure

noncomputable section

namespace SpanMajorisation

open MirabolicMajorantSupport MirabolicMajorantRightTranslate

namespace MirabolicMajorantSpan

variable {F : Type} [Field F] [NumberField F]

private def HasGaugeBound (t : ℕ) (T : Finset (HeightOneSpectrum (𝓞 F))) (B : ℝ)
    (W : AdelicGL 3 (𝓞 F) F → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 F) F, InRootLevel F T B g →
    ‖W g‖ ≤ C / (rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N)

private theorem one_add_archRootSum_pos (g : AdelicGL 3 (𝓞 F) F) : 0 < 1 + archRootSum F g := by
  linarith [archRootSum_nonneg g]

private theorem denom_pos (t N : ℕ) (g : AdelicGL 3 (𝓞 F) F) :
    0 < rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N :=
  mul_pos (pow_pos (rootSizeProd_pos g) t) (pow_pos (one_add_archRootSum_pos g) N)

private theorem inRootLevel_mono {T₁ T : Finset (HeightOneSpectrum (𝓞 F))} (hT : T₁ ⊆ T) {B₁ B : ℝ}
    (hB₁ : B₁ ≤ B) (hB : 1 ≤ B) {g : AdelicGL 3 (𝓞 F) F} (hg : InRootLevel F T₁ B₁ g) :
    InRootLevel F T B g := by
  refine ⟨fun v hv => hg.1 v (fun hv₁ => hv (hT hv₁)), fun v hv => ?_⟩
  by_cases hv₁ : v ∈ T₁
  · exact ⟨(hg.2 v hv₁).1.trans hB₁, (hg.2 v hv₁).2.trans hB₁⟩
  · exact ⟨(hg.1 v hv₁).1.trans hB, (hg.1 v hv₁).2.trans hB⟩

private theorem rootSizeProd_le_of_inRootLevel {T : Finset (HeightOneSpectrum (𝓞 F))} {B : ℝ} (hB : 1 ≤ B)
    {g : AdelicGL 3 (𝓞 F) F} (hg : InRootLevel F T B g) :
    rootSizeProd F g ≤
      B ^ (2 * T.card) * (1 + archRootSum F g) ^ (2 * Fintype.card (InfinitePlace F)) := by
  classical
  have hfin : (∏ᶠ v : HeightOneSpectrum (𝓞 F), finRoot₁ F v g * finRoot₂ F v g) ≤ B ^ (2 * T.card) := by
    have hsub : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => finRoot₁ F v g * finRoot₂ F v g) ⊆
        ↑((mulSupport_finRootProd_finite F g).toFinset ∪ T) := by
      intro v hv
      exact Finset.mem_coe.2
        (Finset.mem_union_left _ ((mulSupport_finRootProd_finite F g).mem_toFinset.mpr hv))
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc (∏ v ∈ (mulSupport_finRootProd_finite F g).toFinset ∪ T, finRoot₁ F v g * finRoot₂ F v g)
        ≤ ∏ v ∈ (mulSupport_finRootProd_finite F g).toFinset ∪ T, (if v ∈ T then B * B else 1) := by
          refine Finset.prod_le_prod (fun v _ => (mul_pos (finRoot₁_pos v g) (finRoot₂_pos v g)).le)
            (fun v _ => ?_)
          by_cases hvT : v ∈ T
          · rw [if_pos hvT]
            exact mul_le_mul (hg.2 v hvT).1 (hg.2 v hvT).2 (finRoot₂_pos v g).le (zero_le_one.trans hB)
          · rw [if_neg hvT]
            exact mul_le_one₀ (hg.1 v hvT).1 (finRoot₂_pos v g).le (hg.1 v hvT).2
      _ = ∏ v ∈ T, (B * B) := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
          congr 1
          ext v
          simp only [Finset.mem_filter, Finset.mem_union, and_iff_right_iff_imp]
          exact fun hv => Or.inr hv
      _ = B ^ (2 * T.card) := by rw [Finset.prod_const, ← sq, ← pow_mul]
  have harch : (∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g) ≤
      (1 + archRootSum F g) ^ (2 * Fintype.card (InfinitePlace F)) := by
    have h1 : ∀ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g ≤ (1 + archRootSum F g) ^ 2 := by
      intro w
      have hw : archRoot₁ F w g + archRoot₂ F w g ≤ archRootSum F g := by
        unfold archRootSum
        exact Finset.single_le_sum (f := fun w : InfinitePlace F => archRoot₁ F w g + archRoot₂ F w g)
          (fun w _ => add_nonneg (archRoot₁_pos w g).le (archRoot₂_pos w g).le) (Finset.mem_univ w)
      have ha := (archRoot₁_pos w g).le
      have hb := (archRoot₂_pos w g).le
      have hS := archRootSum_nonneg g
      nlinarith [mul_nonneg ha hb, mul_nonneg ha ha, mul_nonneg hb hb,
        mul_le_mul hw hw (add_nonneg ha hb) hS]
    calc (∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g)
        ≤ ∏ _w : InfinitePlace F, (1 + archRootSum F g) ^ 2 :=
          Finset.prod_le_prod (fun w _ => (mul_pos (archRoot₁_pos w g) (archRoot₂_pos w g)).le)
            (fun w _ => h1 w)
      _ = (1 + archRootSum F g) ^ (2 * Fintype.card (InfinitePlace F)) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hfin0 : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), finRoot₁ F v g * finRoot₂ F v g :=
    finprod_nonneg fun v => (mul_pos (finRoot₁_pos v g) (finRoot₂_pos v g)).le
  unfold rootSizeProd
  exact mul_le_mul hfin harch
    (Finset.prod_nonneg fun w _ => (mul_pos (archRoot₁_pos w g) (archRoot₂_pos w g)).le)
    (pow_nonneg (zero_le_one.trans hB) _)

private theorem hasGaugeBound_of_mono {t : ℕ} {T₁ T : Finset (HeightOneSpectrum (𝓞 F))} (hT : T₁ ⊆ T)
    {B₁ B : ℝ} (hB₁ : B₁ ≤ B) (hB : 1 ≤ B) {W : AdelicGL 3 (𝓞 F) F → ℂ}
    (h : ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 F) F,
      (¬ InRootLevel F T₁ B₁ g → W g = 0) ∧
        (InRootLevel F T₁ B₁ g → ‖W g‖ ≤ C / (rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N))) :
    (∀ g : AdelicGL 3 (𝓞 F) F, ¬ InRootLevel F T B g → W g = 0) ∧ HasGaugeBound t T B W := by
  refine ⟨fun g hg => ?_, fun N => ?_⟩
  · obtain ⟨C, hC⟩ := h 0
    exact (hC g).1 fun hg₁ => hg (inRootLevel_mono hT hB₁ hB hg₁)
  · obtain ⟨C, hC⟩ := h N
    refine ⟨max C 0, fun g _ => ?_⟩
    by_cases hg₁ : InRootLevel F T₁ B₁ g
    · exact ((hC g).2 hg₁).trans (div_le_div_of_nonneg_right (le_max_left C 0) (denom_pos t N g).le)
    · rw [(hC g).1 hg₁, norm_zero]
      exact div_nonneg (le_max_right C 0) (denom_pos t N g).le

private theorem hasGaugeBound_of_le {t₁ t : ℕ} (ht : t₁ ≤ t) {T : Finset (HeightOneSpectrum (𝓞 F))} {B : ℝ}
    (hB : 1 ≤ B) {W : AdelicGL 3 (𝓞 F) F → ℂ} (h : HasGaugeBound t₁ T B W) : HasGaugeBound t T B W := by
  intro N
  obtain ⟨C, hC⟩ := h (N + 2 * Fintype.card (InfinitePlace F) * (t - t₁))
  refine ⟨max C 0 * B ^ (2 * T.card * (t - t₁)), fun g hg => ?_⟩
  have hP : 0 < rootSizeProd F g := rootSizeProd_pos g
  have hA : 0 < 1 + archRootSum F g := one_add_archRootSum_pos g
  have hW0 : 0 ≤ ‖W g‖ := norm_nonneg _
  have hbox : rootSizeProd F g ^ (t - t₁) ≤
      B ^ (2 * T.card * (t - t₁)) *
        (1 + archRootSum F g) ^ (2 * Fintype.card (InfinitePlace F) * (t - t₁)) := by
    rw [pow_mul B (2 * T.card), pow_mul (1 + archRootSum F g) (2 * Fintype.card (InfinitePlace F)),
      ← mul_pow]
    exact pow_le_pow_left₀ hP.le (rootSizeProd_le_of_inRootLevel hB hg) _
  have h1 : ‖W g‖ * (rootSizeProd F g ^ t₁ *
      (1 + archRootSum F g) ^ (N + 2 * Fintype.card (InfinitePlace F) * (t - t₁))) ≤ max C 0 :=
    ((le_div_iff₀ (denom_pos t₁ _ g)).1 (hC g hg)).trans (le_max_left C 0)
  rw [le_div_iff₀ (denom_pos t N g)]
  have hsplit : rootSizeProd F g ^ t = rootSizeProd F g ^ t₁ * rootSizeProd F g ^ (t - t₁) := by
    rw [← pow_add, Nat.add_sub_cancel' ht]
  rw [hsplit]
  have hB0 : 0 ≤ B ^ (2 * T.card * (t - t₁)) := pow_nonneg (zero_le_one.trans hB) _
  calc ‖W g‖ * (rootSizeProd F g ^ t₁ * rootSizeProd F g ^ (t - t₁) * (1 + archRootSum F g) ^ N)
      = ‖W g‖ * rootSizeProd F g ^ t₁ * (1 + archRootSum F g) ^ N * rootSizeProd F g ^ (t - t₁) := by ring
    _ ≤ ‖W g‖ * rootSizeProd F g ^ t₁ * (1 + archRootSum F g) ^ N *
          (B ^ (2 * T.card * (t - t₁)) *
            (1 + archRootSum F g) ^ (2 * Fintype.card (InfinitePlace F) * (t - t₁))) :=
        mul_le_mul_of_nonneg_left hbox (by positivity)
    _ = (‖W g‖ * (rootSizeProd F g ^ t₁ *
          (1 + archRootSum F g) ^ (N + 2 * Fintype.card (InfinitePlace F) * (t - t₁)))) *
            B ^ (2 * T.card * (t - t₁)) := by
        rw [pow_add]; ring
    _ ≤ max C 0 * B ^ (2 * T.card * (t - t₁)) := mul_le_mul_of_nonneg_right h1 hB0

private theorem hasGaugeBound_add {t : ℕ} {T : Finset (HeightOneSpectrum (𝓞 F))} {B : ℝ}
    {W₁ W₂ : AdelicGL 3 (𝓞 F) F → ℂ} (h₁ : HasGaugeBound t T B W₁) (h₂ : HasGaugeBound t T B W₂) :
    HasGaugeBound t T B (W₁ + W₂) := by
  intro N
  obtain ⟨C₁, hC₁⟩ := h₁ N
  obtain ⟨C₂, hC₂⟩ := h₂ N
  refine ⟨C₁ + C₂, fun g hg => ?_⟩
  rw [Pi.add_apply, add_div]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ g hg) (hC₂ g hg))

private theorem isGaugeMajorised3_of_halves {t : ℕ} {T : Finset (HeightOneSpectrum (𝓞 F))} {B : ℝ}
    {W : AdelicGL 3 (𝓞 F) F → ℂ} (hvan : ∀ g : AdelicGL 3 (𝓞 F) F, ¬ InRootLevel F T B g → W g = 0)
    (hb : HasGaugeBound t T B W) : IsGaugeMajorised3 F W := by
  refine ⟨t, T, B, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  exact ⟨C, fun g => ⟨hvan g, hC g⟩⟩

private theorem isGaugeMajorised3_add {W₁ W₂ : AdelicGL 3 (𝓞 F) F → ℂ} (h₁ : IsGaugeMajorised3 F W₁)
    (h₂ : IsGaugeMajorised3 F W₂) : IsGaugeMajorised3 F (W₁ + W₂) := by
  classical
  obtain ⟨t₁, T₁, B₁, h₁⟩ := h₁
  obtain ⟨t₂, T₂, B₂, h₂⟩ := h₂
  have hB : (1 : ℝ) ≤ max (max B₁ B₂) 1 := le_max_right _ _
  obtain ⟨hv₁, hb₁⟩ := hasGaugeBound_of_mono (T := T₁ ∪ T₂) Finset.subset_union_left
    ((le_max_left B₁ B₂).trans (le_max_left _ 1)) hB h₁
  obtain ⟨hv₂, hb₂⟩ := hasGaugeBound_of_mono (T := T₁ ∪ T₂) Finset.subset_union_right
    ((le_max_right B₁ B₂).trans (le_max_left _ 1)) hB h₂
  refine isGaugeMajorised3_of_halves (t := max t₁ t₂) (T := T₁ ∪ T₂) (B := max (max B₁ B₂) 1)
    (fun g hg => ?_)
    (hasGaugeBound_add (hasGaugeBound_of_le (le_max_left t₁ t₂) hB hb₁)
      (hasGaugeBound_of_le (le_max_right t₁ t₂) hB hb₂))
  rw [Pi.add_apply, hv₁ g hg, hv₂ g hg, add_zero]

end MirabolicMajorantSpan
end SpanMajorisation

end

open SpanMajorisation SpanMajorisation.MirabolicMajorantRightTranslate SpanMajorisation.MirabolicMajorantSpan in
theorem solution (F : Type) [Field F] [NumberField F]
    {W : AdelicGL 3 (𝓞 F) F → ℂ} (hW : IsGaugeMajorised3 F W) {W' : AdelicGL 3 (𝓞 F) F → ℂ}
    (hW' : W' ∈ gl3CyclicSubspace W) : IsGaugeMajorised3 F W' := by
  induction hW' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact isGaugeMajorised3_mul_right hW h
  | zero => exact isGaugeMajorised3_zero F
  | add x y _ _ hx hy => exact isGaugeMajorised3_add hx hy
  | smul c x _ hx => exact MirabolicMajorantClosure.isGaugeMajorised3_const_mul c hx

end S_LanglandsTunnell_CubicInduction_isGaugeMajorised3_of_mem_gl3CyclicSubspace
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isGaugeMajorised3_of_mem_gl3CyclicSubspace (solution)
