-- Prove2me | solution 1 for GeneralizedComplex.exists_of_maximalIsotropic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:42:12.03291+00:00
-- url     : https://prove2.me/submissions/9f074964-ced4-4f5b-83c3-ae6468901d76

import Mathlib
import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GCAux5
open GeneralizedComplex

noncomputable abbrev Jc {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) : Matrix (GIdx N) (GIdx N) ℂ :=
  J.map (fun x : ℝ => (x : ℂ))

lemma mem_plusI {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (v : GIdx N → ℂ) :
    v ∈ plusIEigenspace J ↔ Jc J *ᵥ v = Complex.I • v := by
  simp [plusIEigenspace, sub_eq_zero]

lemma star_mulVec {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (v : GIdx N → ℂ) :
    star (Jc J *ᵥ v) = Jc J *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, Matrix.map_apply]

lemma Jc_sq {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (h : J * J = -1) (v : GIdx N → ℂ) :
    Jc J *ᵥ (Jc J *ᵥ v) = -v := by
  rw [mulVec_mulVec]
  have : Jc J * Jc J = -1 := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply] at this ⊢
    rw [← Complex.ofReal_inj] at this
    push_cast at this
    rw [this]; split_ifs <;> simp
  rw [this, neg_mulVec, one_mulVec]

lemma mem_conj {ι : Type*} (L : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) :
    v ∈ conjSubmodule L ↔ star v ∈ L := Iff.rfl

lemma conj_finrank {ι : Type*} [Fintype ι] (L : Submodule ℂ (ι → ℂ)) :
    Module.finrank ℂ (conjSubmodule L) = Module.finrank ℂ L := by
  let j : L ≃+ conjSubmodule L :=
    { toFun := fun v => ⟨star (v : ι → ℂ), by simp [mem_conj]⟩
      invFun := fun v => ⟨star (v : ι → ℂ), (mem_conj L v).1 v.2⟩
      left_inv := fun v => by simp
      right_inv := fun v => by simp
      map_add' := fun a b => by ext; simp }
  have := rank_eq_of_equiv_equiv (starRingEnd ℂ) j (Function.Involutive.bijective (f := starRingEnd ℂ) Complex.conj_conj) (fun r m => by
    ext i; simp [j])
  unfold Module.finrank; rw [this]

/-- the pairing as a quadratic form with Gram matrix `G` -/
noncomputable def G {𝕜 : Type*} [Field 𝕜] (N : ℕ) : Matrix (GIdx N) (GIdx N) 𝕜 :=
  fromBlocks 0 ((1 / 2 : 𝕜) • 1) ((1 / 2 : 𝕜) • 1) 0

lemma pairing_eq {𝕜 : Type*} [Field 𝕜] {N : ℕ} (u v : GIdx N → 𝕜) :
    pairing u v = u ⬝ᵥ (G N *ᵥ v) := by
  unfold pairing G vecPart formPart
  rw [fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mulVec, zero_add,
    add_zero, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  rw [add_div, Finset.sum_div, Finset.sum_div, add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

lemma quad {𝕜 : Type*} [Field 𝕜] {N : ℕ} (A : Matrix (GIdx N) (GIdx N) 𝕜) (u v : GIdx N → 𝕜) :
    pairing (A *ᵥ u) (A *ᵥ v) = u ⬝ᵥ ((Aᵀ * G N * A) *ᵥ v) := by
  rw [pairing_eq, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Aᵀ, vecMul_transpose]

lemma entry {𝕜 : Type*} [Field 𝕜] {N : ℕ} (M : Matrix (GIdx N) (GIdx N) 𝕜) (i j : GIdx N) :
    M i j = Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) := by
  simp [mulVec, dotProduct, Pi.single_apply]

lemma gram_inv {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J) :
    Jᵀ * G N * J = G N := by
  ext i j
  have := hJ.pairing_mulVec (Pi.single i 1) (Pi.single j 1)
  rw [quad, pairing_eq, ← entry, ← entry] at this
  exact this

lemma G_map {N : ℕ} : (G N : Matrix (GIdx N) (GIdx N) ℝ).map (fun x : ℝ => (x : ℂ)) = G N := by
  ext i j
  cases i <;> cases j <;> simp [G, Matrix.one_apply] <;> split_ifs <;> simp

lemma pairing_c {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J)
    (u v : GIdx N → ℂ) : pairing (Jc J *ᵥ u) (Jc J *ᵥ v) = pairing u v := by
  have h : (Jc J)ᵀ * G N * Jc J = G N := by
    rw [← G_map, Jc, ← transpose_map]
    have h2 := congrArg (fun M => M.map (Complex.ofRealHom : ℝ →+* ℂ)) (gram_inv J hJ)
    simp only [Matrix.map_mul] at h2
    exact h2
  rw [quad, h, pairing_eq]


lemma inf_bot {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) :
    plusIEigenspace J ⊓ conjSubmodule (plusIEigenspace J) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  rw [SetLike.mem_coe, mem_plusI] at h1
  rw [SetLike.mem_coe, mem_conj, mem_plusI, ← star_mulVec, h1, star_smul] at h2
  have h3 := congrArg star h2
  rw [star_smul, star_star, star_star] at h3
  have : (2 * Complex.I) • v = 0 := by
    have e : (2 * Complex.I) • v = Complex.I • v - star Complex.I • v := by
      rw [Complex.star_def, Complex.conj_I]; ext i; simp; ring
    rw [e, h3, star_smul, star_star, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · rw [h]; exact Submodule.zero_mem _

lemma sup_top {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J) :
    plusIEigenspace J ⊔ conjSubmodule (plusIEigenspace J) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  set a := v - Complex.I • (Jc J *ᵥ v) with ha
  set b := v + Complex.I • (Jc J *ᵥ v) with hb
  have hsq := Jc_sq J hJ.sq_eq_neg_one v
  have hIa : Jc J *ᵥ a = Complex.I • a := by
    rw [ha, mulVec_sub, mulVec_smul, hsq, smul_sub, smul_smul, Complex.I_mul_I]
    ext i; simp; try ring
  have hIb : Jc J *ᵥ b = -(Complex.I • b) := by
    rw [hb, mulVec_add, mulVec_smul, hsq, smul_add, smul_smul, Complex.I_mul_I]
    ext i; simp; try ring
  have hsb : Jc J *ᵥ star b = Complex.I • star b := by
    rw [← star_mulVec, hIb, star_neg, star_smul]
    ext i; simp
  have hv : v = (1 / 2 : ℂ) • a + (1 / 2 : ℂ) • b := by
    rw [ha, hb]; ext i; simp; ring
  rw [hv]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ ((mem_plusI J a).2 hIa))
    (Submodule.smul_mem _ _ ((mem_conj _ b).2 ((mem_plusI J _).2 hsb)))

lemma finrank_L {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J) :
    Module.finrank ℂ (plusIEigenspace J) = N := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (plusIEigenspace J)
    (conjSubmodule (plusIEigenspace J))
  rw [sup_top J hJ, inf_bot J, finrank_top, finrank_bot, conj_finrank, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, Fintype.card_fin] at h
  omega

lemma isotropic {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J) :
    IsIsotropic (plusIEigenspace J) := by
  intro u hu v hv
  rw [mem_plusI] at hu hv
  have h := pairing_c J hJ u v
  rw [hu, hv, pairing_eq, pairing_eq, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul,
    Complex.I_mul_I] at h
  have : (2 : ℂ) * (u ⬝ᵥ (G N *ᵥ v)) = 0 := by
    simp only [smul_eq_mul] at h; linear_combination -h
  rw [pairing_eq]
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

theorem properties {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J) :
    plusIEigenspace J ⊓ conjSubmodule (plusIEigenspace J) = ⊥ ∧
      IsMaximalIsotropic (plusIEigenspace J) :=
  ⟨inf_bot J, isotropic J hJ, finrank_L J hJ⟩

theorem genType_le' {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J) :
    genType (plusIEigenspace J) ≤ N := by
  set L := plusIEigenspace J
  set f : (GIdx N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := LinearMap.funLeft ℂ ℂ Sum.inl with hf
  -- kernel of f has dimension N
  have hfs : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    exact ⟨Sum.elim x 0, by ext i; simp [hf, LinearMap.funLeft_apply]⟩
  have hkf : Module.finrank ℂ (LinearMap.ker f) = N := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hfs, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin] at this
    omega
  -- rank-nullity on L
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict L)
  rw [LinearMap.range_domRestrict, finrank_L J hJ] at h1
  set K := (LinearMap.ker (f.domRestrict L)).map L.subtype with hK
  have hKr : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.ker (f.domRestrict L)) :=
    Submodule.finrank_map_subtype_eq _ _
  have hKL : K ≤ L := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have hKf : K ≤ LinearMap.ker f := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hKc : conjSubmodule K ≤ LinearMap.ker f := by
    intro v hv
    have := hKf hv
    rw [LinearMap.mem_ker] at this ⊢
    have e := congrArg star this
    rw [star_zero] at e
    rw [← e]; ext i; simp [hf, LinearMap.funLeft_apply]
  have hinf : K ⊓ conjSubmodule K = ⊥ := by
    rw [eq_bot_iff, ← inf_bot J]
    exact inf_le_inf hKL (fun v hv => hKL hv)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq K (conjSubmodule K)
  rw [hinf, finrank_bot, conj_finrank] at hsup
  have hle : Module.finrank ℂ ↥(K ⊔ conjSubmodule K) ≤ N := by
    calc Module.finrank ℂ ↥(K ⊔ conjSubmodule K) ≤ Module.finrank ℂ (LinearMap.ker f) :=
          Submodule.finrank_mono (sup_le hKf hKc)
      _ = N := hkf
  unfold genType tangentProjection
  rw [← hf]
  omega

end GCAux5

namespace GCAux6
open GeneralizedComplex GCAux5

lemma pairing_add_left {N : ℕ} (a b c : GIdx N → ℂ) : pairing (a + b) c = pairing a c + pairing b c := by
  simp [pairing_eq, add_dotProduct]
lemma pairing_add_right {N : ℕ} (a b c : GIdx N → ℂ) : pairing a (b + c) = pairing a b + pairing a c := by
  simp [pairing_eq, mulVec_add, dotProduct_add]
lemma pairing_smul_left {N : ℕ} (r : ℂ) (a c : GIdx N → ℂ) : pairing (r • a) c = r * pairing a c := by
  simp [pairing_eq, smul_dotProduct]
lemma pairing_smul_right {N : ℕ} (r : ℂ) (a c : GIdx N → ℂ) : pairing a (r • c) = r * pairing a c := by
  simp [pairing_eq, mulVec_smul, dotProduct_smul]
lemma pairing_star {N : ℕ} (a c : GIdx N → ℂ) : pairing (star a) (star c) = star (pairing a c) := by
  unfold pairing vecPart formPart
  simp [dotProduct, map_sum, Finset.sum_div]

lemma pairing_coe {N : ℕ} (u v : GIdx N → ℝ) :
    pairing (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) = ((pairing u v : ℝ) : ℂ) := by
  unfold pairing vecPart formPart
  simp [dotProduct]

theorem exists_J {N : ℕ} (L : Submodule ℂ (GIdx N → ℂ))
    (hL : IsMaximalIsotropic L) (hconj : L ⊓ conjSubmodule L = ⊥) :
    ∃ J : Matrix (GIdx N) (GIdx N) ℝ, IsGenAlmostComplex J ∧ plusIEigenspace J = L := by
  set Lb := conjSubmodule L
  have hcompl : IsCompl L Lb := by
    refine ⟨disjoint_iff.2 hconj, codisjoint_iff.2 ?_⟩
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq L Lb
    rw [hconj, finrank_bot, conj_finrank, hL.2, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin] at *
    omega
  set P : (GIdx N → ℂ) →ₗ[ℂ] (GIdx N → ℂ) :=
    LinearMap.ofIsCompl hcompl (Complex.I • L.subtype) ((-Complex.I) • Lb.subtype) with hP
  have hPL : ∀ a ∈ L, P a = Complex.I • a := fun a ha => by
    have := LinearMap.ofIsCompl_apply_left hcompl (φ := Complex.I • L.subtype)
      (ψ := (-Complex.I) • Lb.subtype) ⟨a, ha⟩
    simpa using this
  have hPLb : ∀ b ∈ Lb, P b = -(Complex.I • b) := fun b hb => by
    have := LinearMap.ofIsCompl_apply_right hcompl (φ := Complex.I • L.subtype)
      (ψ := (-Complex.I) • Lb.subtype) ⟨b, hb⟩
    simpa using this
  have hdec : ∀ v, ∃ a ∈ L, ∃ b ∈ Lb, v = a + b := by
    intro v
    obtain ⟨a, b, h, -⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
    exact ⟨a, a.2, b, b.2, h.symm⟩
  have hreal : ∀ v, P (star v) = star (P v) := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    have hsa : star a ∈ Lb := by show star (star a) ∈ L; rwa [star_star]
    have hsb : star b ∈ L := hb
    rw [star_add, map_add, map_add, hPL _ hsb, hPLb _ hsa, hPL _ ha, hPLb _ hb, star_add, star_neg,
      star_smul, star_smul, Complex.star_def, Complex.conj_I]
    ext i; simp; try ring
  set M := LinearMap.toMatrix' P with hM
  have hMv : ∀ v, M *ᵥ v = P v := fun v => LinearMap.toMatrix'_mulVec P v
  have hMreal : ∀ i j, ((M i j).re : ℂ) = M i j := by
    intro i j
    have e : M i j = P (Pi.single j 1) i := by
      rw [← hMv]; simp [mulVec, dotProduct, Pi.single_apply]
    have hs : star (Pi.single j (1 : ℂ) : GIdx N → ℂ) = Pi.single j 1 := by
      ext k; by_cases h : k = j <;> simp [h]
    have key : starRingEnd ℂ (M i j) = M i j := by
      have := congrFun (hreal (Pi.single j 1)) i
      rw [hs] at this
      rw [e]; nth_rewrite 2 [this]; rfl
    exact Complex.conj_eq_iff_re.1 key
  set J : Matrix (GIdx N) (GIdx N) ℝ := M.map Complex.re with hJ
  have hJc : Jc J = M := by ext i j; simp [hJ, hMreal]
  have hJv : ∀ v, Jc J *ᵥ v = P v := fun v => by rw [hJc, hMv]
  have hPP : ∀ v, P (P v) = -v := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rw [map_add, hPL _ ha, hPLb _ hb, map_add, map_neg, map_smul, map_smul, hPL _ ha, hPLb _ hb,
      smul_smul, smul_neg, smul_smul, Complex.I_mul_I]
    ext i; simp; ring
  have hPpair : ∀ u v, pairing (P u) (P v) = pairing u v := by
    intro u v
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec u
    obtain ⟨c, hc, d, hd, rfl⟩ := hdec v
    have hac : pairing a c = 0 := hL.1 a ha c hc
    have hbd : pairing b d = 0 := by
      have := hL.1 (star b) hb (star d) hd
      rw [pairing_star] at this
      have := congrArg star this
      rwa [star_star, star_zero] at this
    rw [map_add, map_add, hPL _ ha, hPLb _ hb, hPL _ hc, hPLb _ hd, ← neg_smul, ← neg_smul]
    simp only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right, hac, hbd]
    linear_combination (-(pairing a d) - pairing b c) * Complex.I_mul_I
  refine ⟨J, ⟨?_, ?_⟩, ?_⟩
  · ext i j
    have e1 : ((J * J) i j : ℂ) = (Jc J * Jc J) i j := by
      simp [Matrix.mul_apply, Jc]
    have e2 : (Jc J * Jc J) i j = ((-1 : Matrix (GIdx N) (GIdx N) ℝ) i j : ℂ) := by
      rw [GCAux5.entry (Jc J * Jc J) i j, ← mulVec_mulVec, hJv, hJv, hPP]
      simp [dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]
      split_ifs <;> simp
    exact_mod_cast e1.trans e2
  · intro u v
    have := hPpair (fun i => (u i : ℂ)) (fun i => (v i : ℂ))
    rw [← hJv, ← hJv] at this
    have h1 : Jc J *ᵥ (fun i => (u i : ℂ)) = fun i => ((J *ᵥ u) i : ℂ) := by
      ext i; simp [mulVec, dotProduct]
    have h2 : Jc J *ᵥ (fun i => (v i : ℂ)) = fun i => ((J *ᵥ v) i : ℂ) := by
      ext i; simp [mulVec, dotProduct]
    rw [h1, h2, pairing_coe, pairing_coe] at this
    exact_mod_cast this
  · ext v
    rw [mem_plusI, hJv]
    constructor
    · intro h
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
      rw [map_add, hPL _ ha, hPLb _ hb, smul_add] at h
      have h' : -(Complex.I • b) = Complex.I • b := by
        have := congrArg (fun w => w - Complex.I • a) h; simpa using this
      have hb0 : b = 0 := by
        ext i
        have := congrFun h' i
        simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this
        have h2 : Complex.I * b i = 0 := by linear_combination -this / 2
        simpa [Complex.I_ne_zero] using h2
      rw [hb0, add_zero]; exact ha
    · intro hv; exact hPL v hv

end GCAux6
namespace GCAux
open GeneralizedComplex

noncomputable abbrev Jc {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) : Matrix (GIdx N) (GIdx N) ℂ :=
  J.map (fun x : ℝ => (x : ℂ))

lemma mem_plusI {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (v : GIdx N → ℂ) :
    v ∈ plusIEigenspace J ↔ Jc J *ᵥ v = Complex.I • v := by
  simp [plusIEigenspace, sub_eq_zero]

lemma star_mulVec {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (v : GIdx N → ℂ) :
    star (Jc J *ᵥ v) = Jc J *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, Matrix.map_apply]

lemma Jc_sq {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (h : J * J = -1) (v : GIdx N → ℂ) :
    Jc J *ᵥ (Jc J *ᵥ v) = -v := by
  rw [mulVec_mulVec]
  have : Jc J * Jc J = -1 := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply] at this ⊢
    rw [← Complex.ofReal_inj] at this
    push_cast at this
    rw [this]; split_ifs <;> simp
  rw [this, neg_mulVec, one_mulVec]

lemma eq_of_eq {N : ℕ} (J₁ J₂ : Matrix (GIdx N) (GIdx N) ℝ)
    (h₁ : IsGenAlmostComplex J₁) (h : plusIEigenspace J₁ = plusIEigenspace J₂) : J₁ = J₂ := by
  have key : ∀ v, Jc J₁ *ᵥ v = Jc J₂ *ᵥ v := by
    intro v
    set a := v - Complex.I • (Jc J₁ *ᵥ v) with ha
    set b := v + Complex.I • (Jc J₁ *ᵥ v) with hb
    have hsq := Jc_sq J₁ h₁.sq_eq_neg_one v
    have hIa : Jc J₁ *ᵥ a = Complex.I • a := by
      rw [ha, mulVec_sub, mulVec_smul, hsq, smul_sub, smul_smul, Complex.I_mul_I]
      ext i; simp; try ring
    have hIb : Jc J₁ *ᵥ b = -(Complex.I • b) := by
      rw [hb, mulVec_add, mulVec_smul, hsq, smul_add, smul_smul, Complex.I_mul_I]
      ext i; simp; try ring
    have ha2 : Jc J₂ *ᵥ a = Complex.I • a := (mem_plusI J₂ a).1 (h ▸ (mem_plusI J₁ a).2 hIa)
    have hsb : Jc J₁ *ᵥ star b = Complex.I • star b := by
      rw [← star_mulVec, hIb, star_neg, star_smul]
      ext i; simp [Complex.conj_I]
    have hsb2 : Jc J₂ *ᵥ star b = Complex.I • star b := (mem_plusI J₂ _).1 (h ▸ (mem_plusI J₁ _).2 hsb)
    have hb2 : Jc J₂ *ᵥ b = -(Complex.I • b) := by
      have := congrArg star hsb2
      rw [star_mulVec, star_star, star_smul, star_star] at this
      rw [this]; ext i; simp
    have hv : v = (1 / 2 : ℂ) • (a + b) := by
      rw [ha, hb]; ext i; simp; ring
    have e1 : Jc J₂ *ᵥ v = (1 / 2 : ℂ) • (Complex.I • a - Complex.I • b) := by
      rw [hv, mulVec_smul, mulVec_add, ha2, hb2, sub_eq_add_neg]
    rw [e1, ha, hb]
    ext i; simp; ring_nf; rw [Complex.I_sq]; ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simp [mulVec, dotProduct, Pi.single_apply] at this
  exact_mod_cast this

end GCAux

open GeneralizedComplex in
theorem solution {N : ℕ} (L : Submodule ℂ (GIdx N → ℂ))
    (hL : IsMaximalIsotropic L) (hconj : L ⊓ conjSubmodule L = ⊥) :
    ∃ J : Matrix (GIdx N) (GIdx N) ℝ, IsGenAlmostComplex J ∧ plusIEigenspace J = L :=
  GCAux6.exists_J L hL hconj
