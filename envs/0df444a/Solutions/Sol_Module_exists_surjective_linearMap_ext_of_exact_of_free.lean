-- Prove2me | solution 1 for Module.exists_surjective_linearMap_ext_of_exact_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e4540ab4-715a-5cf1-b92b-a26cb454afdd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_surjective_linearMap_ext_of_exact_of_free

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace F3cBridge

variable {R : Type u} [CommRing R]
variable (P : ℕ → Type u) [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
  (e : ∀ n, P (n + 1) →ₗ[R] P n) (hee : ∀ n, e n ∘ₗ e (n + 1) = 0)

noncomputable abbrev cx : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (P n)) (fun n => ModuleCat.ofHom (e n))
    (fun n => by
      ext x
      have := congrArg (fun φ : P (n + 1 + 1) →ₗ[R] P n => φ x) (hee n)
      simpa using this)

theorem ofd (j : ℕ) :
    ChainComplex.of.d (fun n => ModuleCat.of R (P n)) (fun n => ModuleCat.ofHom (e n)) (j + 1) j =
      ModuleCat.ofHom (e j) :=
  ChainComplex.of_d _ _ j

theorem ofd10 :
    ChainComplex.of.d (fun n => ModuleCat.of R (P n)) (fun n => ModuleCat.ofHom (e n)) 1 0 =
      ModuleCat.ofHom (e 0) :=
  ofd P e 0

theorem ofd21 (m : ℕ) :
    ChainComplex.of.d (fun n => ModuleCat.of R (P n)) (fun n => ModuleCat.ofHom (e n)) (m + 2) (m + 1) =
      ModuleCat.ofHom (e (m + 1)) :=
  ofd P e (m + 1)

theorem cxd10 : (cx P e hee).d 1 0 = ModuleCat.ofHom (e 0) := ofd P e 0

theorem cxd (j : ℕ) : (cx P e hee).d (j + 1) j = ModuleCat.ofHom (e j) := ofd P e j

variable (X : Type u) [AddCommGroup X] [Module R X] (π0 : P 0 →ₗ[R] X) (hπ0 : π0 ∘ₗ e 0 = 0)

noncomputable def aug :
    cx P e hee ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R X) :=
  ((cx P e hee).toSingle₀Equiv _).symm
    ⟨ModuleCat.ofHom π0, by
      rw [cxd10]
      ext x
      simpa using congrArg (fun φ : P 1 →ₗ[R] X => φ x) hπ0⟩

theorem aug_f_zero : (aug P e hee X π0 hπ0).f 0 = ModuleCat.ofHom π0 := by
  simp [aug, ChainComplex.toSingle₀Equiv]

theorem quasiIso_aug (hex : ∀ n, LinearMap.ker (e n) = LinearMap.range (e (n + 1)))
    (hker : LinearMap.ker π0 = LinearMap.range (e 0)) (hsurj : Function.Surjective π0) :
    QuasiIso (aug P e hee X π0 hπ0) where
  quasiIsoAt m := by
    induction m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      constructor
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, aug_f_zero,
          HomologicalComplex.shortComplexFunctor'_obj_f]
        rw [ofd10]
        have h__af := hker.symm
        simp at h__af
        exact h__af
      · rw [ModuleCat.epi_iff_surjective]
        simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, aug_f_zero]
        exact hsurj
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
          HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
          ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simp only [HomologicalComplex.shortComplexFunctor'_obj_f, HomologicalComplex.shortComplexFunctor'_obj_g]
      erw [ofd21, ofd]
      exact (hex m).symm

variable [∀ n, Module.Projective R (P n)]
variable (hex : ∀ n, LinearMap.ker (e n) = LinearMap.range (e (n + 1)))
    (hker : LinearMap.ker π0 = LinearMap.range (e 0)) (hsurj : Function.Surjective π0)

noncomputable def res : ProjectiveResolution (ModuleCat.of R X) where
  complex := cx P e hee
  projective n := (ModuleCat.of R (P n)).projective_of_categoryTheory_projective
  π := aug P e hee X π0 hπ0
  quasiIso := quasiIso_aug P e hee X π0 hπ0 hex hker hsurj

variable (M : Type u) [AddCommGroup M] [Module R M]

noncomputable def toExt (j : ℕ) (f : P j →ₗ[R] M) (hf : f ∘ₗ e j = 0) :
    Abelian.Ext.{u} (ModuleCat.of R X) (ModuleCat.of R M) j :=
  (res P e hee X π0 hπ0 hex hker hsurj).extMk (ModuleCat.ofHom f) (j + 1) rfl (by
    change (cx P e hee).d (j + 1) j ≫ ModuleCat.ofHom f = 0
    rw [cxd]
    ext x
    simpa using congrArg (fun φ : P (j + 1) →ₗ[R] M => φ x) hf)

theorem toExt_add (j : ℕ) (f g : P j →ₗ[R] M) (hf : f ∘ₗ e j = 0) (hg : g ∘ₗ e j = 0) :
    toExt P e hee X π0 hπ0 hex hker hsurj M j (f + g) (by rw [LinearMap.add_comp, hf, hg, add_zero]) =
      toExt P e hee X π0 hπ0 hex hker hsurj M j f hf + toExt P e hee X π0 hπ0 hex hker hsurj M j g hg := by
  unfold toExt
  rw [ProjectiveResolution.add_extMk]
  rfl

theorem toExt_smul (j : ℕ) (r : R) (f : P j →ₗ[R] M) (hf : f ∘ₗ e j = 0) :
    toExt P e hee X π0 hπ0 hex hker hsurj M j (r • f) (by rw [LinearMap.smul_comp, hf, smul_zero]) =
      r • toExt P e hee X π0 hπ0 hex hker hsurj M j f hf := by
  unfold toExt
  rw [Abelian.Ext.smul_eq_comp_mk₀, ProjectiveResolution.extMk_comp_mk₀]
  congr 1

theorem toExt_surjective (j : ℕ) (α : Abelian.Ext.{u} (ModuleCat.of R X) (ModuleCat.of R M) j) :
    ∃ (f : P j →ₗ[R] M) (hf : f ∘ₗ e j = 0), toExt P e hee X π0 hπ0 hex hker hsurj M j f hf = α := by
  obtain ⟨f', hf', h⟩ := (res P e hee X π0 hπ0 hex hker hsurj).extMk_surjective α (j + 1) rfl
  have hf'' : (cx P e hee).d (j + 1) j ≫ f' = 0 := hf'
  rw [cxd] at hf''
  refine ⟨f'.hom, ?_, ?_⟩
  · ext x
    have := congrArg (fun φ => ModuleCat.Hom.hom φ x) hf''
    simp at this
    exact this
  · exact h

theorem toExt_eq_zero_iff (p : ℕ) (f : P (p + 1) →ₗ[R] M) (hf : f ∘ₗ e (p + 1) = 0) :
    toExt P e hee X π0 hπ0 hex hker hsurj M (p + 1) f hf = 0 ↔
      ∃ ψ : P p →ₗ[R] M, f = ψ ∘ₗ e p := by
  unfold toExt
  rw [ProjectiveResolution.extMk_eq_zero_iff _ _ _ _ _ p rfl]
  change (∃ g : (cx P e hee).X p ⟶ ModuleCat.of R M, (cx P e hee).d (p + 1) p ≫ g = ModuleCat.ofHom f) ↔ _
  rw [cxd]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.hom, ?_⟩
    have := congrArg ModuleCat.Hom.hom hg
    simpa [ModuleCat.hom_comp] using this.symm
  · rintro ⟨ψ, rfl⟩
    exact ⟨ModuleCat.ofHom ψ, by ext x; simp⟩

end F3cBridge

namespace F3cInst

variable (R : Type u) [CommRing R]
variable (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]

def kc {a b : ℕ} (h : a = b) : K a ≃ₗ[R] K b := h ▸ LinearEquiv.refl R (K a)

@[scoped simp] theorem kc_self_eq {a : ℕ} (h : a = a) : kc R K h = LinearEquiv.refl R (K a) := rfl

@[scoped simp] theorem kc_self {a : ℕ} (h : a = a) (x : K a) : kc R K h x = x := rfl

@[scoped simp] theorem kc_kc {a b c : ℕ} (h1 : a = b) (h2 : b = c) (x : K a) :
    kc R K h2 (kc R K h1 x) = kc R K (h1.trans h2) x := by
  subst h1; subst h2; rfl

theorem kc_symm {a b : ℕ} (h : a = b) : (kc R K h).symm = kc R K h.symm := by
  subst h; rfl

@[scoped simp] theorem kc_symm_apply {a b : ℕ} (h : a = b) (y : K b) :
    (kc R K h).symm y = kc R K h.symm y := by
  subst h; rfl

variable (δ : ∀ i, K i →ₗ[R] K (i + 1))

@[scoped simp] theorem delta_kc {a b : ℕ} (h : a = b) (x : K a) :
    δ b (kc R K h x) = kc R K (congrArg (fun t => t + 1) h) (δ a x) := by
  subst h; rfl

variable (n : ℕ)

def ee (j : ℕ) : K (n + 1 - (j + 1)) →ₗ[R] K (n + 1 - j) :=
  if hj : j ≤ n then
    (kc R K (show n - j + 1 = n + 1 - j by omega)).toLinearMap ∘ₗ δ (n - j) ∘ₗ
      (kc R K (show n + 1 - (j + 1) = n - j by omega)).toLinearMap
  else if (j - n) % 2 = 0 then (kc R K (show n + 1 - (j + 1) = n + 1 - j by omega)).toLinearMap
  else 0

theorem ee_of_le {j : ℕ} (hj : j ≤ n) : ee R K δ n j =
    (kc R K (show n - j + 1 = n + 1 - j by omega)).toLinearMap ∘ₗ δ (n - j) ∘ₗ
      (kc R K (show n + 1 - (j + 1) = n - j by omega)).toLinearMap := by
  rw [ee, dif_pos hj]

theorem ee_apply_of_le {j : ℕ} (hj : j ≤ n) (x : K (n + 1 - (j + 1))) : ee R K δ n j x =
    kc R K (show n - j + 1 = n + 1 - j by omega) (δ (n - j) (kc R K (show n + 1 - (j + 1) = n - j by omega) x)) := by
  rw [ee_of_le R K δ n hj]; rfl

theorem ee_of_gt_even {j : ℕ} (hj : n < j) (hp : (j - n) % 2 = 0) : ee R K δ n j =
    (kc R K (show n + 1 - (j + 1) = n + 1 - j by omega)).toLinearMap := by
  rw [ee, dif_neg (by omega), if_pos hp]

theorem ee_of_gt_odd {j : ℕ} (hj : n < j) (hp : (j - n) % 2 = 1) : ee R K δ n j = 0 := by
  rw [ee, dif_neg (by omega), if_neg (by omega)]

variable (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)

include hdd in
theorem hdd' (i : ℕ) (x : K i) : δ (i + 1) (δ i x) = 0 :=
  congrArg (fun φ : K i →ₗ[R] K (i + 1 + 1) => φ x) (hdd i)

include hdd in
theorem ee_comp_ee (j : ℕ) : ee R K δ n j ∘ₗ ee R K δ n (j + 1) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rcases Nat.lt_or_ge n (j + 1) with h | h
  ·
    rcases Nat.lt_or_ge n j with h' | h'
    ·
      by_cases hp : (j - n) % 2 = 0
      · rw [ee_of_gt_odd R K δ n h (by omega), LinearMap.zero_apply, map_zero]
      · rw [ee_of_gt_odd R K δ n h' (by omega), LinearMap.zero_apply]
    ·
      rw [ee_of_gt_odd R K δ n h (by omega), LinearMap.zero_apply, map_zero]
  ·
    rw [ee_apply_of_le R K δ n h, ee_apply_of_le R K δ n (by omega)]
    simp [hdd' R K δ hdd]

variable (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
  (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))

include hex0 in
theorem aux_ex0 (a : ℕ) (ha : a = 0) (y : K a) (hy : δ a y = 0) : y = 0 := by
  subst ha; exact hex0 y hy

include hex in
theorem aux_ex (a i : ℕ) (hi : i < n) (ha : a = i + 1) (y : K a) (hy : δ a y = 0) :
    ∃ w : K i, kc R K ha.symm (δ i w) = y := by
  subst ha
  obtain ⟨w, hw⟩ := hex i hi y hy
  exact ⟨w, by simpa using hw⟩

include hdd hex0 hex in
theorem ker_ee (j : ℕ) : LinearMap.ker (ee R K δ n j) = LinearMap.range (ee R K δ n (j + 1)) := by
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    rcases Nat.lt_or_ge n (j + 1) with h | h
    · rcases Nat.lt_or_ge n j with h' | h'
      · by_cases hp : (j - n) % 2 = 0
        · rw [ee_of_gt_even R K δ n h' hp] at hz
          have : z = 0 := by simpa using hz
          subst this; exact Submodule.zero_mem _
        · refine ⟨kc R K (show n + 1 - (j + 1) = n + 1 - (j + 1 + 1) by omega) z, ?_⟩
          rw [ee_of_gt_even R K δ n h (by omega)]
          simp
      ·
        obtain rfl : n = j := by omega
        rw [ee_apply_of_le R K δ n le_rfl] at hz
        have hz' := congrArg (kc R K (show n + 1 - n = n - n + 1 by omega)) hz
        rw [kc_kc, kc_self, map_zero] at hz'
        have := aux_ex0 R K δ hex0 (n - n) (by omega) _ hz'
        have : z = 0 := by simpa using congrArg (kc R K (show n - n = n + 1 - (n + 1) by omega)) this
        subst this; exact Submodule.zero_mem _
    ·
      rw [ee_apply_of_le R K δ n (by omega : j ≤ n)] at hz
      have hz' := congrArg (kc R K (show n + 1 - j = n - j + 1 by omega)) hz
      rw [kc_kc, kc_self, map_zero] at hz'
      obtain ⟨w, hw⟩ := aux_ex R K δ n hex (n - j) (n - (j + 1)) (by omega) (by omega) _ hz'
      refine ⟨kc R K (show n - (j + 1) = n + 1 - (j + 1 + 1) by omega) w, ?_⟩
      rw [ee_apply_of_le R K δ n h]
      have hw' := congrArg (kc R K (show n - j = n + 1 - (j + 1) by omega)) hw
      simp only [kc_kc, kc_self] at hw'
      simpa using hw'
  · rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ee_comp_ee R K δ n hdd, LinearMap.zero_apply]

def pi0 : K (n + 1 - 0) →ₗ[R] K (n + 1) ⧸ LinearMap.range (δ n) :=
  (LinearMap.range (δ n)).mkQ ∘ₗ (kc R K (show n + 1 - 0 = n + 1 by omega)).toLinearMap

theorem aux_pi0 (a b : ℕ) (ha : a = n) (hb : b = n + 1) (h1 : a + 1 = b) (y : K a) :
    kc R K hb (kc R K h1 (δ a y)) ∈ LinearMap.range (δ n) := by
  subst ha; subst hb; exact ⟨y, by simp⟩

theorem aux_pi0' (a b : ℕ) (ha : a = n) (hb : b = n + 1) (h1 : a + 1 = b) (z : K b)
    (hz : kc R K hb z ∈ LinearMap.range (δ n)) : ∃ y : K a, kc R K h1 (δ a y) = z := by
  subst ha; subst hb
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, by simpa using hy⟩

theorem pi0_comp_ee : pi0 R K δ n ∘ₗ ee R K δ n 0 = 0 := by
  ext x
  simp only [pi0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply,
    ee_apply_of_le R K δ n (Nat.zero_le n), Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact aux_pi0 R K δ n (n - 0) (n + 1 - 0) (by omega) (by omega) (by omega) _

theorem ker_pi0 : LinearMap.ker (pi0 R K δ n) = LinearMap.range (ee R K δ n 0) := by
  ext z
  simp only [pi0, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := aux_pi0' R K δ n (n - 0) (n + 1 - 0) (by omega) (by omega) (by omega) z hz
    refine ⟨kc R K (show n - 0 = n + 1 - 1 by omega) y, ?_⟩
    rw [ee_apply_of_le R K δ n (Nat.zero_le n)]
    simpa using hy
  · rintro ⟨x, rfl⟩
    rw [ee_apply_of_le R K δ n (Nat.zero_le n)]
    exact aux_pi0 R K δ n (n - 0) (n + 1 - 0) (by omega) (by omega) (by omega) _

theorem pi0_surjective : Function.Surjective (pi0 R K δ n) :=
  (Submodule.mkQ_surjective _).comp (kc R K (show n + 1 - 0 = n + 1 by omega)).surjective

end F3cInst
p2m_reactivate "P2MW.S_Module_exists_surjective_linearMap_ext_of_exact_of_free.F3cInst"

namespace F3cBridge

theorem toExt_congr {R : Type u} [CommRing R]
    (P : ℕ → Type u) [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
    (e : ∀ n, P (n + 1) →ₗ[R] P n) (hee : ∀ n, e n ∘ₗ e (n + 1) = 0)
    (X : Type u) [AddCommGroup X] [Module R X] (π0 : P 0 →ₗ[R] X) (hπ0 : π0 ∘ₗ e 0 = 0)
    [∀ n, Module.Projective R (P n)]
    (hex : ∀ n, LinearMap.ker (e n) = LinearMap.range (e (n + 1)))
    (hker : LinearMap.ker π0 = LinearMap.range (e 0)) (hsurj : Function.Surjective π0)
    (M : Type u) [AddCommGroup M] [Module R M] (j : ℕ) {F G : P j →ₗ[R] M} (h : F = G)
    (hF : F ∘ₗ e j = 0) (hG : G ∘ₗ e j = 0) :
    toExt P e hee X π0 hπ0 hex hker hsurj M j F hF = toExt P e hee X π0 hπ0 hex hker hsurj M j G hG := by
  subst h; rfl

end F3cBridge
p2m_reactivate "P2MW.S_Module_exists_surjective_linearMap_ext_of_exact_of_free.F3cInst"

namespace F3cInst

variable (R : Type u) [CommRing R]
variable (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Free R (K i)]
variable (δ : ∀ i, K i →ₗ[R] K (i + 1)) (n : ℕ)
  (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
  (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
  (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
variable (M : Type u) [AddCommGroup M] [Module R M]

scoped instance projP (j : ℕ) : Module.Projective R (K (n + 1 - j)) := Module.Projective.of_free

noncomputable def TE (j : ℕ) (f : K (n + 1 - j) →ₗ[R] M) (hf : f ∘ₗ ee R K δ n j = 0) :
    Abelian.Ext.{u} (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) j :=
  F3cBridge.toExt (fun j => K (n + 1 - j)) (ee R K δ n) (ee_comp_ee R K δ n hdd)
    (K (n + 1) ⧸ LinearMap.range (δ n)) (pi0 R K δ n) (pi0_comp_ee R K δ n)
    (ker_ee R K δ n hdd hex0 hex) (ker_pi0 R K δ n) (pi0_surjective R K δ n) M j f hf

theorem TE_congr (j : ℕ) {F G : K (n + 1 - j) →ₗ[R] M} (h : F = G)
    (hF : F ∘ₗ ee R K δ n j = 0) (hG : G ∘ₗ ee R K δ n j = 0) :
    TE R K δ n hdd hex0 hex M j F hF = TE R K δ n hdd hex0 hex M j G hG := by
  subst h; rfl

theorem TE_add (j : ℕ) (f g : K (n + 1 - j) →ₗ[R] M) (hf : f ∘ₗ ee R K δ n j = 0)
    (hg : g ∘ₗ ee R K δ n j = 0) (hfg : (f + g) ∘ₗ ee R K δ n j = 0) :
    TE R K δ n hdd hex0 hex M j (f + g) hfg =
      TE R K δ n hdd hex0 hex M j f hf + TE R K δ n hdd hex0 hex M j g hg :=
  F3cBridge.toExt_add ..

theorem TE_smul (j : ℕ) (r : R) (f : K (n + 1 - j) →ₗ[R] M) (hf : f ∘ₗ ee R K δ n j = 0)
    (hrf : (r • f) ∘ₗ ee R K δ n j = 0) :
    TE R K δ n hdd hex0 hex M j (r • f) hrf = r • TE R K δ n hdd hex0 hex M j f hf :=
  F3cBridge.toExt_smul ..

theorem TE_surjective (j : ℕ)
    (α : Abelian.Ext.{u} (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) j) :
    ∃ (f : K (n + 1 - j) →ₗ[R] M) (hf : f ∘ₗ ee R K δ n j = 0), TE R K δ n hdd hex0 hex M j f hf = α := by
  obtain ⟨f, hf, h⟩ := F3cBridge.toExt_surjective (fun j => K (n + 1 - j)) (ee R K δ n) (ee_comp_ee R K δ n hdd)
    (K (n + 1) ⧸ LinearMap.range (δ n)) (pi0 R K δ n) (pi0_comp_ee R K δ n)
    (ker_ee R K δ n hdd hex0 hex) (ker_pi0 R K δ n) (pi0_surjective R K δ n) M j α
  exact ⟨f, hf, h⟩

theorem TE_eq_zero_iff (p : ℕ) (f : K (n + 1 - (p + 1)) →ₗ[R] M) (hf : f ∘ₗ ee R K δ n (p + 1) = 0) :
    TE R K δ n hdd hex0 hex M (p + 1) f hf = 0 ↔ ∃ ψ : K (n + 1 - p) →ₗ[R] M, f = ψ ∘ₗ ee R K δ n p :=
  F3cBridge.toExt_eq_zero_iff ..

omit hdd hex0 hex

omit [∀ i, Module.Free R (K i)] in
theorem aux_top (a c b : ℕ) (ha : 0 = a) (hc : 0 = c) (hb : c + 1 = b) (h2 : a = c)
    (f : K 0 →ₗ[R] M) :
    (∃ ψ : K b →ₗ[R] M, f ∘ₗ (kc R K ha).symm.toLinearMap =
        ψ ∘ₗ ((kc R K hb).toLinearMap ∘ₗ δ c ∘ₗ (kc R K h2).toLinearMap)) ↔
      ∃ ψ' : K 1 →ₗ[R] M, ψ' ∘ₗ δ 0 = f := by
  subst ha; subst hc; subst hb
  simp only [kc_self_eq, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
    LinearMap.id_comp]
  exact ⟨fun ⟨ψ, h⟩ => ⟨ψ, h.symm⟩, fun ⟨ψ, h⟩ => ⟨ψ, h.symm⟩⟩

omit [∀ i, Module.Free R (K i)] in
theorem aux_coc (i c a d : ℕ) (hc : i = c) (hd : i = d) (ha : i + 1 = a) (h1 : c + 1 = a) (h2 : d = c)
    (φ : K (i + 1) →ₗ[R] M) (hφ : φ ∘ₗ δ i = 0) :
    (φ ∘ₗ (kc R K ha).symm.toLinearMap) ∘ₗ ((kc R K h1).toLinearMap ∘ₗ δ c ∘ₗ (kc R K h2).toLinearMap) = 0 := by
  subst hc; subst hd; subst ha
  simpa only [kc_self_eq, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
    LinearMap.id_comp] using hφ

omit [∀ i, Module.Free R (K i)] in
theorem aux_coc' (i c a d : ℕ) (hc : i = c) (hd : i = d) (ha : i + 1 = a) (h1 : c + 1 = a) (h2 : d = c)
    (F : K a →ₗ[R] M) (hF : F ∘ₗ ((kc R K h1).toLinearMap ∘ₗ δ c ∘ₗ (kc R K h2).toLinearMap) = 0) :
    (F ∘ₗ (kc R K ha).toLinearMap) ∘ₗ δ i = 0 := by
  subst hc; subst hd; subst ha
  simpa only [kc_self_eq, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
    LinearMap.id_comp] using hF

omit [∀ i, Module.Free R (K i)] in
theorem aux_ker (i a c b : ℕ) (ha : i + 1 = a) (hc : i + 1 = c) (hb : c + 1 = b) (h2 : a = c)
    (φ : K (i + 1) →ₗ[R] M) :
    (∃ ψ : K b →ₗ[R] M, φ ∘ₗ (kc R K ha).symm.toLinearMap =
        ψ ∘ₗ ((kc R K hb).toLinearMap ∘ₗ δ c ∘ₗ (kc R K h2).toLinearMap)) ↔
      ∃ ψ' : K (i + 2) →ₗ[R] M, φ = ψ' ∘ₗ δ (i + 1) := by
  subst ha; subst hc; subst hb
  simp only [kc_self_eq, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
    LinearMap.id_comp]

end F3cInst
p2m_reactivate "P2MW.S_Module_exists_surjective_linearMap_ext_of_exact_of_free.F3cInst"

open F3cInst in
theorem solution
    (R : Type u) [CommRing R] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Free R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (M : Type u) [AddCommGroup M] [Module R M] :
    (∃ π : (K 0 →ₗ[R] M) →ₗ[R]
        Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n + 1),
      Function.Surjective π ∧ LinearMap.ker π = LinearMap.range (LinearMap.lcomp R M (δ 0))) ∧
    ∀ i : ℕ, i < n →
      ∃ π : LinearMap.ker (LinearMap.lcomp R M (δ i) : (K (i + 1) →ₗ[R] M) →ₗ[R] (K i →ₗ[R] M)) →ₗ[R]
          Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n - i),
        Function.Surjective π ∧
          ∀ φ, π φ = 0 ↔ ∃ ψ : K (i + 2) →ₗ[R] M, (φ : K (i + 1) →ₗ[R] M) = ψ ∘ₗ δ (i + 1) := by
  constructor
  ·
    let c0 : K 0 ≃ₗ[R] K (n + 1 - (n + 1)) := kc R K (by omega)
    have hz : ee R K δ n (n + 1) = 0 := ee_of_gt_odd R K δ n (Nat.lt_succ_self n) (by omega)
    have hcoc : ∀ f : K 0 →ₗ[R] M, (f ∘ₗ c0.symm.toLinearMap) ∘ₗ ee R K δ n (n + 1) = 0 := fun f => by
      rw [hz, LinearMap.comp_zero]
    let π : (K 0 →ₗ[R] M) →ₗ[R]
        Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (n + 1) :=
      { toFun := fun f => TE R K δ n hdd hex0 hex M (n + 1) (f ∘ₗ c0.symm.toLinearMap) (hcoc f)
        map_add' := fun f g => by
          rw [← TE_add R K δ n hdd hex0 hex M (n + 1) _ _ (hcoc f) (hcoc g)
            (by rw [← LinearMap.add_comp]; exact hcoc (f + g))]
          exact TE_congr R K δ n hdd hex0 hex M (n + 1) (LinearMap.add_comp _ _ _) _ _
        map_smul' := fun r f => by
          simp only [RingHom.id_apply]
          rw [← TE_smul R K δ n hdd hex0 hex M (n + 1) r _ (hcoc f)
            (by rw [← LinearMap.smul_comp]; exact hcoc (r • f))]
          exact TE_congr R K δ n hdd hex0 hex M (n + 1) (LinearMap.smul_comp _ _ _) _ _ }
    refine ⟨π, ?_, ?_⟩
    · intro α
      obtain ⟨F, hF, hFa⟩ := TE_surjective R K δ n hdd hex0 hex M (n + 1) α
      refine ⟨F ∘ₗ c0.toLinearMap, ?_⟩
      change TE R K δ n hdd hex0 hex M (n + 1) ((F ∘ₗ c0.toLinearMap) ∘ₗ c0.symm.toLinearMap)
        (hcoc (F ∘ₗ c0.toLinearMap)) = α
      rw [← hFa]
      exact TE_congr R K δ n hdd hex0 hex M (n + 1) (by ext x; simp) _ _
    · ext f
      rw [LinearMap.mem_ker, LinearMap.mem_range]
      change TE R K δ n hdd hex0 hex M (n + 1) (f ∘ₗ c0.symm.toLinearMap) (hcoc f) = 0 ↔ _
      rw [TE_eq_zero_iff, ee_of_le R K δ n le_rfl]
      exact aux_top R K δ M (n + 1 - (n + 1)) (n - n) (n + 1 - n) (by omega) (by omega) (by omega)
        (by omega) f
  · intro i hi
    obtain ⟨p, hp⟩ : ∃ p, n - i = p + 1 := ⟨n - i - 1, by omega⟩
    rw [hp]
    let cA : K (i + 1) ≃ₗ[R] K (n + 1 - (p + 1)) := kc R K (by omega)
    have hcoc : ∀ φ : LinearMap.ker (LinearMap.lcomp R M (δ i) : (K (i + 1) →ₗ[R] M) →ₗ[R] (K i →ₗ[R] M)),
        ((φ : K (i + 1) →ₗ[R] M) ∘ₗ cA.symm.toLinearMap) ∘ₗ ee R K δ n (p + 1) = 0 := fun φ => by
      rw [ee_of_le R K δ n (by omega : p + 1 ≤ n)]
      exact aux_coc R K δ M i (n - (p + 1)) (n + 1 - (p + 1)) (n + 1 - (p + 1 + 1)) (by omega) (by omega)
        (by omega) (by omega) (by omega) φ (LinearMap.mem_ker.mp φ.2)
    let π : LinearMap.ker (LinearMap.lcomp R M (δ i) : (K (i + 1) →ₗ[R] M) →ₗ[R] (K i →ₗ[R] M)) →ₗ[R]
        Abelian.Ext (ModuleCat.of R (K (n + 1) ⧸ LinearMap.range (δ n))) (ModuleCat.of R M) (p + 1) :=
      { toFun := fun φ => TE R K δ n hdd hex0 hex M (p + 1) ((φ : K (i + 1) →ₗ[R] M) ∘ₗ cA.symm.toLinearMap) (hcoc φ)
        map_add' := fun φ ψ => by
          rw [← TE_add R K δ n hdd hex0 hex M (p + 1) _ _ (hcoc φ) (hcoc ψ)
            (by rw [← LinearMap.add_comp, ← Submodule.coe_add]; exact hcoc (φ + ψ))]
          exact TE_congr R K δ n hdd hex0 hex M (p + 1) (by rw [Submodule.coe_add, LinearMap.add_comp]) _ _
        map_smul' := fun r φ => by
          simp only [RingHom.id_apply]
          rw [← TE_smul R K δ n hdd hex0 hex M (p + 1) r _ (hcoc φ)
            (by rw [← LinearMap.smul_comp, ← Submodule.coe_smul]; exact hcoc (r • φ))]
          exact TE_congr R K δ n hdd hex0 hex M (p + 1) (by rw [Submodule.coe_smul, LinearMap.smul_comp]) _ _ }
    refine ⟨π, ?_, ?_⟩
    · intro α
      obtain ⟨F, hF, hFa⟩ := TE_surjective R K δ n hdd hex0 hex M (p + 1) α
      have hF' : (F ∘ₗ cA.toLinearMap) ∘ₗ δ i = 0 := by
        rw [ee_of_le R K δ n (by omega : p + 1 ≤ n)] at hF
        exact aux_coc' R K δ M i (n - (p + 1)) (n + 1 - (p + 1)) (n + 1 - (p + 1 + 1)) (by omega) (by omega)
          (by omega) (by omega) (by omega) F hF
      refine ⟨⟨F ∘ₗ cA.toLinearMap, LinearMap.mem_ker.mpr hF'⟩, ?_⟩
      change TE R K δ n hdd hex0 hex M (p + 1) ((F ∘ₗ cA.toLinearMap) ∘ₗ cA.symm.toLinearMap)
        (hcoc ⟨F ∘ₗ cA.toLinearMap, LinearMap.mem_ker.mpr hF'⟩) = α
      rw [← hFa]
      exact TE_congr R K δ n hdd hex0 hex M (p + 1) (by ext x; simp) _ _
    · intro φ
      change TE R K δ n hdd hex0 hex M (p + 1) ((φ : K (i + 1) →ₗ[R] M) ∘ₗ cA.symm.toLinearMap) (hcoc φ) = 0 ↔ _
      rw [TE_eq_zero_iff, ee_of_le R K δ n (by omega : p ≤ n)]
      exact aux_ker R K δ M i (n + 1 - (p + 1)) (n - p) (n + 1 - p) (by omega) (by omega) (by omega)
        (by omega) φ

end S_Module_exists_surjective_linearMap_ext_of_exact_of_free
end P2MW
export P2MW.S_Module_exists_surjective_linearMap_ext_of_exact_of_free (solution)
