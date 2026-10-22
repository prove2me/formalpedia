-- Prove2me | solution 1 for NewtonCartan.isFlat_of_mapsConn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:33:26.227413+00:00
-- url     : https://prove2.me/submissions/906fe710-90a9-4235-a85e-90da432507da

import Mathlib
import Definitions.Def_NewtonCartan_defs

open scoped ContDiff
open NewtonCartan

lemma g72c_cd_pd {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (n : Fin 4) : ContDiff ℝ ∞ (pd φ n) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  exact h1.clm_apply contDiff_const

lemma g72c_cd_comp {Γ : Conn} (hΓ : ContDiff ℝ ∞ Γ) (a b c : Fin 4) :
    ContDiff ℝ ∞ (fun y => Γ y a b c) := by
  have h1 : ContDiff ℝ ∞ (fun y => Γ y a) := (contDiff_pi.1 hΓ) a
  have h2 : ContDiff ℝ ∞ (fun y => Γ y a b) := (contDiff_pi.1 h1) b
  exact (contDiff_pi.1 h2) c

lemma g72c_pd_add {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (b : Fin 4) : pd (fun y => f y + g y) b x = pd f b x + pd g b x := by
  simp only [pd]; rw [fderiv_fun_add hf hg]; rfl

lemma g72c_pd_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (b : Fin 4) : pd (fun y => f y * g y) b x = pd f b x * g x + f x * pd g b x := by
  simp only [pd]; rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

lemma g72c_pd_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℝ} {x : E}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) x) (b : Fin 4) :
    pd (fun y => ∑ i ∈ s, A i y) b x = ∑ i ∈ s, pd (A i) b x := by
  simp only [pd]; rw [fderiv_fun_sum h]; simp [ContinuousLinearMap.sum_apply]

lemma g72c_schwarz {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (b c : Fin 4) (x : E) :
    pd (fun y => pd φ c y) b x = pd (fun y => pd φ b y) c x := by
  have key : ∀ b c : Fin 4, pd (fun y => pd φ c y) b x =
      fderiv ℝ (fderiv ℝ φ) x (Pi.single b 1) (Pi.single c 1) := by
    intro b c
    have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
    have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := h1.differentiable (by simp) x
    simp only [pd]
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast (le_top : (2:ℕ∞) ≤ ⊤)
    | norm_num
    | decide)) _ _

lemma g72c_chain {g : E → ℝ} {f : E → E} {x : E} (hg : DifferentiableAt ℝ g (f x))
    (hf : DifferentiableAt ℝ f x) (d : Fin 4) :
    pd (fun y => g (f y)) d x = ∑ m, pd g m (f x) * pd (fun y => f y m) d x := by
  have hv : fderiv ℝ f x (Pi.single d 1) =
      ∑ m, (fderiv ℝ (fun y => f y m) x (Pi.single d 1)) • (Pi.single m (1:ℝ) : E) := by
    ext i
    simp only [fderiv_apply hf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [pd]
  rw [show (fun y => g (f y)) = g ∘ f from rfl, fderiv_comp x hg hf,
    ContinuousLinearMap.comp_apply]
  rw [hv, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]

lemma g72c_R1 (X : Fin 4 → Fin 4 → Fin 4 → ℝ) (A B C : Fin 4 → ℝ) :
    ∑ s, ∑ r, ∑ m, X r s m * A s * B r * C m = ∑ p, ∑ q, (∑ m, X p q m * C m) * B p * A q := by
  simp only [Fin.sum_univ_four]; ring

lemma g72c_R2 (X : Fin 4 → Fin 4 → Fin 4 → ℝ) (A B C : Fin 4 → ℝ) :
    ∑ s, ∑ r, ∑ m, X m s r * A s * B r * C m = ∑ p, ∑ q, (∑ m, X p q m * B m) * C p * A q := by
  simp only [Fin.sum_univ_four]; ring

lemma g72c_R3 (X : Fin 4 → Fin 4 → ℝ) (Y : Fin 4 → Fin 4 → Fin 4 → ℝ) (A B C : Fin 4 → ℝ) :
    ∑ s, ∑ r, ∑ m, (∑ e, X m e * Y e r s) * A s * B r * C m
      = ∑ p, ∑ q, X p q * C p * (∑ r, ∑ s, Y q r s * B r * A s) := by
  simp only [Fin.sum_univ_four]; ring

lemma g72c_R4 (X : Fin 4 → Fin 4 → ℝ) (Y : Fin 4 → Fin 4 → Fin 4 → ℝ) (A B C : Fin 4 → ℝ) :
    ∑ s, ∑ r, ∑ m, (∑ e, X r e * Y e m s) * A s * B r * C m
      = ∑ p, ∑ q, X p q * B p * (∑ r, ∑ s, Y q r s * C r * A s) := by
  simp only [Fin.sum_univ_four]; ring

lemma g72c_R5 (X : Fin 4 → Fin 4 → ℝ) (B : Fin 4 → Fin 4 → ℝ) (C : Fin 4 → ℝ) :
    ∑ e, (∑ p, ∑ q, X p q * B q e) * C e = ∑ p, ∑ q, X p q * ∑ e, B q e * C e := by
  simp only [Fin.sum_univ_four]; ring

lemma g72c_algB (J : Fin 4 → Fin 4 → ℝ) (DJ G G' : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (DG' : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h1 : ∀ q b c, ∑ e, J q e * G e c b = DJ q b c + ∑ r, ∑ s, G' q r s * J r c * J s b)
    (hDJ : ∀ p c d, DJ p c d = DJ p d c) (a b c d : Fin 4) :
    (∑ p, ∑ q, (((∑ m, DG' a p q m * J m d) * J p c + G' a p q * DJ p c d) * J q b
        + G' a p q * J p c * DJ q b d))
    - (∑ p, ∑ q, (((∑ m, DG' a p q m * J m c) * J p d + G' a p q * DJ p d c) * J q b
        + G' a p q * J p d * DJ q b c))
    + ∑ e, (∑ p, ∑ q, G' a p q * J p d * J q e) * G e c b
    - ∑ e, (∑ p, ∑ q, G' a p q * J p c * J q e) * G e d b
    = ∑ s, ∑ r, ∑ m, (DG' a r s m - DG' a m s r
        + ∑ e, (G' a m e * G' e r s - G' a r e * G' e m s)) * J s b * J r c * J m d := by
  rw [g72c_R5 (fun p q => G' a p q * J p d) J (fun e => G e c b),
    g72c_R5 (fun p q => G' a p q * J p c) J (fun e => G e d b)]
  simp only [h1]
  have hR : ∑ s, ∑ r, ∑ m, (DG' a r s m - DG' a m s r
        + ∑ e, (G' a m e * G' e r s - G' a r e * G' e m s)) * J s b * J r c * J m d
      = ∑ p, ∑ q, (∑ m, DG' a p q m * J m d) * J p c * J q b
        - ∑ p, ∑ q, (∑ m, DG' a p q m * J m c) * J p d * J q b
        + (∑ p, ∑ q, G' a p q * J p d * (∑ r, ∑ s, G' q r s * J r c * J s b)
          - ∑ p, ∑ q, G' a p q * J p c * (∑ r, ∑ s, G' q r s * J r d * J s b)) := by
    rw [← g72c_R1 (DG' a) (fun s => J s b) (fun r => J r c) (fun m => J m d),
      ← g72c_R2 (DG' a) (fun s => J s b) (fun r => J r c) (fun m => J m d),
      ← g72c_R3 (G' a) G' (fun s => J s b) (fun r => J r c) (fun m => J m d),
      ← g72c_R4 (G' a) G' (fun s => J s b) (fun r => J r c) (fun m => J m d)]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun r _ =>
      Finset.sum_congr rfl (fun m _ => ?_)))
    rw [Finset.sum_sub_distrib]; ring
  rw [hR]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [hDJ p c d]
  ring

lemma g72c_algA (J : Fin 4 → Fin 4 → ℝ) (DJ G K : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (DDJ DG DK : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h1 : ∀ a b c, DJ a c b + K a b c = ∑ n, J a n * G n b c)
    (h2 : ∀ a b c d, DDJ a c b d + DK a b c d = ∑ n, (DJ a n d * G n b c + J a n * DG n b c d))
    (hDDJ : ∀ a b c d, DDJ a b c d = DDJ a b d c) (a b c d : Fin 4) :
    ∑ n, J a n * (DG n c b d - DG n d b c + ∑ e, (G n d e * G e c b - G n c e * G e d b)) =
      DK a c b d - DK a d b c + ∑ e, K a d e * G e c b - ∑ e, K a c e * G e d b := by
  have e1 := h2 a c b d
  have e2 := h2 a d b c
  have e3 := hDDJ a b c d
  have f0 := h1 a d 0
  have f1 := h1 a d 1
  have f2 := h1 a d 2
  have f3 := h1 a d 3
  have g0 := h1 a c 0
  have g1 := h1 a c 1
  have g2 := h1 a c 2
  have g3 := h1 a c 3
  simp only [Fin.sum_univ_four] at e1 e2 f0 f1 f2 f3 g0 g1 g2 g3 ⊢
  linear_combination e2 - e1 + e3 - G 0 c b * f0 - G 1 c b * f1 - G 2 c b * f2 - G 3 c b * f3
    + G 0 d b * g0 + G 1 d b * g1 + G 2 d b * g2 + G 3 d b * g3


lemma g72c_inj (f : E ≃ E) (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ f.symm) (x : E)
    (v : Fin 4 → ℝ) (hv : ∀ a, ∑ n, pd (fun y => f y a) n x * v n = 0) : v = 0 := by
  have hdf : DifferentiableAt ℝ f x := hfs.differentiable (by simp) x
  have hdg : DifferentiableAt ℝ f.symm (f x) := hgs.differentiable (by simp) (f x)
  have hL : fderiv ℝ f x v = 0 := by
    have hsum : v = ∑ n, v n • (Pi.single n (1:ℝ) : E) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    ext a
    rw [hsum, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hv a]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_comm]
    congr 1
    simp only [pd, fderiv_apply hdf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have hcomp : fderiv ℝ (f.symm ∘ f) x = (fderiv ℝ f.symm (f x)).comp (fderiv ℝ f x) :=
    fderiv_comp x hdg hdf
  have hid : (f.symm ∘ f) = id := funext fun y => f.symm_apply_apply y
  rw [hid, fderiv_id] at hcomp
  have := congrArg (fun L => L v) hcomp
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, hL, map_zero] at this
  exact this

theorem solution (f : E ≃ E) (hf : IsDiffeo f) (Γ Γ' : Conn) (hΓ : IsDerivOp Γ)
    (hΓ' : IsDerivOp Γ') (hm : MapsConn f Γ Γ') (hfl : IsFlat Γ') : IsFlat Γ := by
  obtain ⟨hfs, hgs⟩ := hf
  have hfc : ∀ a, ContDiff ℝ ∞ (fun y => f y a) := fun a => contDiff_pi.1 hfs a
  have hJ : ∀ a b, ContDiff ℝ ∞ (fun y => pd (fun z => f z a) b y) :=
    fun a b => g72c_cd_pd (hfc a) b
  have hG : ∀ a b c, ContDiff ℝ ∞ (fun y => Γ y a b c) := g72c_cd_comp hΓ.1
  have hG' : ∀ a b c, ContDiff ℝ ∞ (fun y => Γ' y a b c) := g72c_cd_comp hΓ'.1
  have hG'f : ∀ a b c, ContDiff ℝ ∞ (fun y => Γ' (f y) a b c) := fun a b c => (hG' a b c).comp hfs
  have hd : ∀ {g : E → ℝ}, ContDiff ℝ ∞ g → ∀ x, DifferentiableAt ℝ g x :=
    fun h x => h.differentiable (by simp) x
  intro x a b c d
  have dG'f : ∀ a p q, DifferentiableAt ℝ (fun y => Γ' (f y) a p q) x := fun a p q => hd (hG'f a p q) x
  have dJ : ∀ a b, DifferentiableAt ℝ (fun y => pd (fun z => f z a) b y) x := fun a b => hd (hJ a b) x
  have hKc : ∀ a b c, ContDiff ℝ ∞ (fun y => ∑ p, ∑ q, Γ' (f y) a p q * pd (fun w => f w p) b y
      * pd (fun w => f w q) c y) := by
    intro a b c
    exact ContDiff.sum fun p _ => ContDiff.sum fun q _ => ((hG'f a p q).mul (hJ p b)).mul (hJ q c)
  have key : ∀ a, ∑ n, pd (fun y => f y a) n x * riem Γ x n b c d = 0 := by
    intro a
    have hm' : ∀ y a b c, pd (fun z => pd (fun w => f w a) c z) b y
        + ∑ p, ∑ q, Γ' (f y) a p q * pd (fun w => f w p) b y * pd (fun w => f w q) c y
        = ∑ n, pd (fun w => f w a) n y * Γ y n b c := fun y a b c => hm y a b c
    have h2 : ∀ a b c d,
        pd (fun y => pd (fun z => pd (fun w => f w a) c z) b y) d x
        + pd (fun y => ∑ p, ∑ q, Γ' (f y) a p q * pd (fun w => f w p) b y
            * pd (fun w => f w q) c y) d x
        = ∑ n, (pd (fun y => pd (fun w => f w a) n y) d x * Γ x n b c
            + pd (fun w => f w a) n x * pd (fun y => Γ y n b c) d x) := by
      intro a b c d
      have e := congrArg (fun F => pd F d x) (funext fun y => hm' y a b c)
      try simp only at e
      rw [g72c_pd_add (hd (g72c_cd_pd (hJ a c) b) x) (hd (hKc a b c) x),
        g72c_pd_sum _ (fun n _ => hd ((hJ a n).mul (hG n b c)) x)] at e
      exact e.trans (Finset.sum_congr rfl fun n _ => g72c_pd_mul (dJ a n) (hd (hG n b c) x) d)
    have hDK : ∀ a b c d,
        pd (fun y => ∑ p, ∑ q, Γ' (f y) a p q * pd (fun w => f w p) b y
            * pd (fun w => f w q) c y) d x
        = ∑ p, ∑ q, (((∑ m, pd (fun y => Γ' y a p q) m (f x) * pd (fun w => f w m) d x)
            * pd (fun w => f w p) b x + Γ' (f x) a p q * pd (fun y => pd (fun w => f w p) b y) d x)
            * pd (fun w => f w q) c x
            + Γ' (f x) a p q * pd (fun w => f w p) b x * pd (fun y => pd (fun w => f w q) c y) d x) := by
      intro a b c d
      rw [g72c_pd_sum]
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [g72c_pd_sum]
        · refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [g72c_pd_mul (hd ((hG'f a p q).mul (hJ p b)) x) (hd (hJ q c) x), g72c_pd_mul (hd (hG'f a p q) x) (hd (hJ p b) x)]
          have hc := g72c_chain (g := fun y => Γ' y a p q) (f := f) (x := x)
            (hd (hG' a p q) (f x)) (hfs.differentiable (by simp) x) d
          try simp only at hc
          rw [hc]
        · intro q _; exact hd (((hG'f a p q).mul (hJ p b)).mul (hJ q c)) x
      · intro p _
        exact hd (ContDiff.sum fun q _ => ((hG'f a p q).mul (hJ p b)).mul (hJ q c)) x
    have A := g72c_algA (fun i j => pd (fun w => f w i) j x)
      (fun i j k => pd (fun y => pd (fun w => f w i) j y) k x) (Γ x)
      (fun i j k => ∑ p, ∑ q, Γ' (f x) i p q * pd (fun w => f w p) j x * pd (fun w => f w q) k x)
      (fun i j k l => pd (fun y => pd (fun z => pd (fun w => f w i) j z) k y) l x)
      (fun n i j k => pd (fun y => Γ y n i j) k x)
      (fun i j k l => pd (fun y => ∑ p, ∑ q, Γ' (f y) i p q * pd (fun w => f w p) j y
            * pd (fun w => f w q) k y) l x)
      (fun a b c => hm' x a b c) (fun a b c d => h2 a b c d)
      (fun a b c d => g72c_schwarz (hJ a b) d c x) a b c d
    have B := g72c_algB (fun i j => pd (fun w => f w i) j x)
      (fun i j k => pd (fun y => pd (fun w => f w i) j y) k x) (Γ x) (Γ' (f x))
      (fun i p q m => pd (fun y => Γ' y i p q) m (f x))
      (fun q b c => (hm' x q c b).symm) (fun p c d => g72c_schwarz (hfc p) d c x) a b c d
    beta_reduce at A B
    rw [hDK a c b d, hDK a d b c] at A
    refine Eq.trans ?_ (A.trans (B.trans ?_))
    · rfl
    · refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun r _ =>
        Finset.sum_eq_zero fun m _ => ?_
      have hz := hfl (f x) a s r m
      simp only [riem] at hz
      rw [hz]; ring
  have := g72c_inj f hfs hgs x (fun n => riem Γ x n b c d) key
  exact congrFun this a
